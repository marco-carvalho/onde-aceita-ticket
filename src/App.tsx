import {
  hashKey,
  QueryClient,
  QueryClientProvider,
  skipToken,
  useQuery,
  useQueryClient,
} from '@tanstack/react-query';
import {
  useCallback,
  useEffect,
  useId,
  useRef,
  useState,
  type KeyboardEvent,
  type ReactElement,
} from 'react';

const MAX_RADIUS = 10_000;
const DEFAULT_RADIUS = 500;
const MAX_PAGE_SIZE = 1000;
const MAX_PAGES = 10;

const BENEFITS = ['RESTAURANTE', 'ALIMENTACAO'] as const;

const MAX_TARGETS = 25;
const MAX_TERM_LENGTH = 120;
const DEFAULT_SLEEP_MS = 300;
const PAGE_SLEEP_MS = 900;

const MAX_REGEX_LENGTH = 200;

const REQUEST_TIMEOUT_MS = 25_000;
const GEOCODE_DEBOUNCE_MS = 400;
const GEOCODE_MIN_CHARS = 3;

const API_URL = 'https://api.ticket.edenred.com/digital_accredited_network/v2/merchant-benefit';
const NOMINATIM_URL = 'https://nominatim.openstreetmap.org/search';
const NOMINATIM_REVERSE_URL = 'https://nominatim.openstreetmap.org/reverse';

const HEADERS = {
  accept: 'application/json, text/plain, */*',
  authorization: 'Bearer',
  'content-type': 'application/json',
  'x-mobile-agent': 'WEB',
};

type Benefit = (typeof BENEFITS)[number];

const BENEFIT_LABEL: Record<Benefit, string> = {
  RESTAURANTE: 'RESTAURANTE',
  ALIMENTACAO: 'ALIMENTAÇÃO',
};

interface Merchant {
  cnpj: string;
  fantasyName: string;
  address: string;
  contact: string;
  latitude: number | null;
  longitude: number | null;
  distanciaMetros: number;
  benefits: string[];
}

interface SearchParams {
  latitude: number;
  longitude: number;
  radius: number;
  benefits: Benefit[];
}

type MatchRange = readonly [start: number, end: number];

interface MerchantHit {
  merchant: Merchant;
  match: MatchRange | null;
}

interface TargetResult {
  term: string;
  hits: MerchantHit[];
}

interface SweepMeta {
  total: number;
  reach: number;
  truncated: boolean;
}

interface SearchOutcome {
  results: TargetResult[];
  sweep: SweepMeta | null;
  listing: MerchantHit[] | null;
}

class ApiError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'ApiError';
  }
}

class PatternError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'PatternError';
  }
}

class InvalidParamsError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'InvalidParamsError';
  }
}

function stripAccents(text: string): string {
  return text.normalize('NFD').replace(/\p{Mn}/gu, '');
}

function norm(text: string): string {
  return stripAccents(text).toUpperCase();
}

function keepsLength(original: string, normalized: string): boolean {
  return original.length === normalized.length;
}

const METACHARACTERS = /[.*+?^${}()|[\]\\]/;

function escapeLiteral(text: string): string {
  return text.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function looksLikeRegex(term: string): boolean {
  return METACHARACTERS.test(term);
}

function buildPattern(term: string): RegExp {
  const trimmed = term.trim();
  if (!trimmed) throw new PatternError('termo vazio');

  if (!looksLikeRegex(trimmed)) {
    if (trimmed.length > MAX_TERM_LENGTH) {
      throw new PatternError(`termo maior que ${MAX_TERM_LENGTH} caracteres`);
    }
    return new RegExp(`\\b${escapeLiteral(norm(trimmed))}`);
  }

  if (trimmed.length > MAX_REGEX_LENGTH) {
    throw new PatternError(`expressão maior que ${MAX_REGEX_LENGTH} caracteres`);
  }
  try {
    return new RegExp(stripAccents(trimmed), 'i');
  } catch {
    throw new PatternError(`expressão regular inválida em "${term}"`);
  }
}

function selectHits(merchants: readonly Merchant[], pattern: RegExp): MerchantHit[] {
  const hits: MerchantHit[] = [];
  for (const merchant of merchants) {
    const normalized = norm(merchant.fantasyName);
    const found = pattern.exec(normalized);
    if (!found) continue;
    const range =
      keepsLength(merchant.fantasyName, normalized) && found[0].length > 0
        ? ([found.index, found.index + found[0].length] as const)
        : null;
    hits.push({ merchant, match: range });
  }
  return hits.sort((a, b) => a.merchant.distanciaMetros - b.merchant.distanciaMetros);
}

const NAME_ALLOWED = /^[A-Z0-9 .,&'()/-]*$/;

function clampInt(value: number, min: number, max: number, field: string): number {
  if (!Number.isFinite(value)) throw new InvalidParamsError(`${field} deve ser um número`);
  return Math.min(max, Math.max(min, Math.round(value)));
}

function coordinate(value: number, limit: number, field: string): number {
  if (!Number.isFinite(value) || value < -limit || value > limit) {
    throw new InvalidParamsError(`${field} fora do intervalo válido`);
  }
  return value;
}

function pickBenefits(selected: readonly Benefit[]): Benefit[] {
  const allowed = selected.filter((benefit) => BENEFITS.includes(benefit));
  if (allowed.length === 0) throw new InvalidParamsError('escolha ao menos um benefício');
  return [...new Set(allowed)];
}

function sanitizeName(term: string): string {
  const name = norm(term).trim().slice(0, MAX_TERM_LENGTH);
  if (!NAME_ALLOWED.test(name)) {
    throw new InvalidParamsError('o termo tem caracteres que a API não aceita no filtro');
  }
  return name;
}

interface SearchPayload extends SearchParams {
  name: string;
  pageSize: number;
  page: number;
  recentlyRegisteredMerchant: false;
}

function buildPayload(params: SearchParams, name: string, page: number): SearchPayload {
  return {
    name,
    radius: clampInt(params.radius, 100, MAX_RADIUS, 'raio'),
    longitude: coordinate(params.longitude, 180, 'longitude'),
    latitude: coordinate(params.latitude, 90, 'latitude'),
    pageSize: MAX_PAGE_SIZE,
    page: clampInt(page, 1, MAX_PAGES, 'página'),
    benefits: pickBenefits(params.benefits),
    recentlyRegisteredMerchant: false,
  };
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null;
}

function parseMerchants(payload: unknown): Merchant[] {
  if (!isRecord(payload) || payload.success !== true) {
    throw new ApiError('A API da Ticket recusou a consulta.');
  }
  if (!Array.isArray(payload.value)) return [];

  const merchants: Merchant[] = [];
  for (const item of payload.value) {
    if (!isRecord(item) || typeof item.fantasyName !== 'string') continue;
    merchants.push({
      cnpj: typeof item.cnpj === 'string' ? item.cnpj : '',
      fantasyName: item.fantasyName,
      address: typeof item.address === 'string' ? item.address : '',
      contact: typeof item.contact === 'string' ? item.contact : '',
      latitude: typeof item.latitude === 'number' ? item.latitude : null,
      longitude: typeof item.longitude === 'number' ? item.longitude : null,
      distanciaMetros: typeof item.distanciaMetros === 'number' ? item.distanciaMetros : 0,
      benefits: Array.isArray(item.benefits)
        ? item.benefits.filter((benefit): benefit is string => typeof benefit === 'string')
        : [],
    });
  }
  return merchants;
}

async function fetchMerchants(
  params: SearchParams,
  name: string,
  page: number,
  signal?: AbortSignal,
): Promise<Merchant[]> {
  const timeout = AbortSignal.timeout(REQUEST_TIMEOUT_MS);
  let response: Response;
  try {
    response = await fetch(API_URL, {
      method: 'POST',
      headers: HEADERS,
      body: JSON.stringify(buildPayload(params, name, page)),
      referrerPolicy: 'no-referrer',
      signal: signal ? AbortSignal.any([signal, timeout]) : timeout,
    });
  } catch (error) {
    if (signal?.aborted) throw error;
    if (error instanceof DOMException && error.name === 'TimeoutError') {
      throw new ApiError('A API da Ticket demorou demais para responder.');
    }
    throw new ApiError('Não foi possível falar com a API da Ticket. Verifique a conexão.');
  }

  if (!response.ok) {
    throw new ApiError(`A API da Ticket respondeu com erro (HTTP ${response.status}).`);
  }

  try {
    return parseMerchants(await response.json());
  } catch (error) {
    if (error instanceof ApiError) throw error;
    throw new ApiError('A resposta da API veio em formato inesperado.');
  }
}

interface PagedMerchants {
  merchants: Merchant[];
  truncated: boolean;
}

function merchantKey(merchant: Merchant): string {
  return `${merchant.cnpj}|${merchant.address}|${merchant.distanciaMetros}`;
}

async function fetchAllPages(
  params: SearchParams,
  name: string,
  signal?: AbortSignal,
  onPage?: (page: number) => void,
): Promise<PagedMerchants> {
  const merchants: Merchant[] = [];
  const seen = new Set<string>();

  for (let page = 1; page <= MAX_PAGES; page += 1) {
    onPage?.(page);
    const batch = await fetchMerchants(params, name, page, signal);
    if (batch.length === 0) return { merchants, truncated: false };

    for (const merchant of batch) {
      const key = merchantKey(merchant);
      if (seen.has(key)) continue;
      seen.add(key);
      merchants.push(merchant);
    }
    if (page < MAX_PAGES) await sleep(PAGE_SLEEP_MS, signal);
  }
  return { merchants, truncated: true };
}

interface SearchProgress {
  done: number;
  total: number;
  page: number;
}

interface SearchRequest {
  params: SearchParams;
  terms: readonly string[];
  signal?: AbortSignal;
  onProgress?: (progress: SearchProgress) => void;
}

interface Compiled {
  term: string;
  pattern: RegExp;
  isRegex: boolean;
}

function sleep(ms: number, signal?: AbortSignal): Promise<void> {
  return new Promise((resolve, reject) => {
    const abort = (): void => {
      reject(new DOMException('consulta cancelada', 'AbortError'));
    };
    if (signal?.aborted) {
      abort();
      return;
    }
    const timer = setTimeout(() => {
      signal?.removeEventListener('abort', onAbort);
      resolve();
    }, ms);
    function onAbort(): void {
      clearTimeout(timer);
      abort();
    }
    signal?.addEventListener('abort', onAbort, { once: true });
  });
}

function cleanTerms(terms: readonly string[]): string[] {
  const unique = new Map<string, string>();
  for (const term of terms) {
    const trimmed = term.trim();
    if (trimmed) unique.set(trimmed.toUpperCase(), trimmed);
  }
  return [...unique.values()].slice(0, MAX_TARGETS);
}

function needsSweep(terms: readonly string[], regexCount: number): boolean {
  return terms.length === 0 || regexCount > 0;
}

function plannedRequests(terms: readonly string[]): number {
  const clean = cleanTerms(terms);
  const regexCount = clean.filter(looksLikeRegex).length;
  return clean.length - regexCount + (needsSweep(clean, regexCount) ? 1 : 0);
}

function sweepMeta(page: PagedMerchants): SweepMeta {
  return {
    total: page.merchants.length,
    reach: page.merchants.reduce((max, merchant) => Math.max(max, merchant.distanciaMetros), 0),
    truncated: page.truncated,
  };
}

async function runSearch(request: SearchRequest): Promise<SearchOutcome> {
  const terms = cleanTerms(request.terms);
  const compiled: Compiled[] = terms.map((term) => ({
    term,
    pattern: buildPattern(term),
    isRegex: looksLikeRegex(term),
  }));

  const regexes = compiled.filter((item) => item.isRegex);
  const literals = compiled.filter((item) => !item.isRegex);
  const total = literals.length + (needsSweep(terms, regexes.length) ? 1 : 0);

  const hitsByTerm = new Map<string, MerchantHit[]>();
  let sweep: SweepMeta | null = null;
  let listing: MerchantHit[] | null = null;
  let done = 0;

  const trackPage = (page: number): void => {
    request.onProgress?.({ done, total, page });
  };
  const finishStep = (): void => {
    request.onProgress?.({ done: ++done, total, page: 0 });
  };

  if (needsSweep(terms, regexes.length)) {
    const paged = await fetchAllPages(request.params, '', request.signal, trackPage);
    sweep = sweepMeta(paged);

    if (terms.length === 0) {
      listing = [...paged.merchants]
        .sort((a, b) => a.distanciaMetros - b.distanciaMetros)
        .map((merchant) => ({ merchant, match: null }));
    }
    for (const item of regexes) {
      hitsByTerm.set(item.term, selectHits(paged.merchants, item.pattern));
    }

    finishStep();
    if (literals.length > 0) await sleep(DEFAULT_SLEEP_MS, request.signal);
  }

  for (const [index, item] of literals.entries()) {
    const paged = await fetchAllPages(
      request.params,
      sanitizeName(item.term),
      request.signal,
      trackPage,
    );
    hitsByTerm.set(item.term, selectHits(paged.merchants, item.pattern));
    finishStep();
    if (index < literals.length - 1) await sleep(DEFAULT_SLEEP_MS, request.signal);
  }

  return {
    results: compiled.map((item) => ({ term: item.term, hits: hitsByTerm.get(item.term) ?? [] })),
    sweep,
    listing,
  };
}

const KM = new Intl.NumberFormat('pt-BR', { maximumFractionDigits: 1 });

function formatDistance(meters: number): string {
  if (!Number.isFinite(meters) || meters < 0) return 'distância desconhecida';
  return meters < 1000 ? `${Math.round(meters)} m` : `${KM.format(meters / 1000)} km`;
}

function formatCnpj(cnpj: string): string | null {
  const digits = cnpj.replace(/\D/g, '');
  if (digits.length !== 14) return null;
  return digits.replace(/^(\d{2})(\d{3})(\d{3})(\d{4})(\d{2})$/, '$1.$2.$3/$4-$5');
}

function telHref(contact: string): string | null {
  const digits = contact.replace(/\D/g, '');
  if (digits.length < 10 || digits.length > 15) return null;
  return `tel:+${digits}`;
}

function walkUrl(merchant: Merchant): string {
  const { latitude, longitude, fantasyName, address } = merchant;
  const destination =
    latitude !== null && longitude !== null
      ? `${latitude},${longitude}`
      : `${fantasyName} ${address}`;
  return `https://www.google.com/maps/dir/?api=1&destination=${encodeURIComponent(destination)}&travelmode=walking`;
}

function Highlight({ text, range }: { text: string; range: MatchRange | null }): ReactElement {
  if (!range) return <>{text}</>;
  const [start, end] = range;
  if (start < 0 || end > text.length || start >= end) return <>{text}</>;

  return (
    <>
      {text.slice(0, start)}
      <mark className="rounded bg-red-500/30 px-0.5 text-red-300">
        {text.slice(start, end)}
      </mark>
      {text.slice(end)}
    </>
  );
}

function HitRow({ hit }: { hit: MerchantHit }): ReactElement {
  const { merchant } = hit;
  const phone = telHref(merchant.contact);
  const cnpj = formatCnpj(merchant.cnpj);

  return (
    <li className="flex flex-col gap-1 border-t border-white/5 px-4 py-3 sm:flex-row sm:items-start sm:justify-between sm:gap-4">
      <div className="min-w-0">
        <p className="font-medium text-stone-100">
          <Highlight text={merchant.fantasyName} range={hit.match} />
        </p>
        {merchant.address && <p className="text-sm text-stone-400">{merchant.address}</p>}
        <div className="mt-1.5 flex flex-wrap items-center gap-x-3 gap-y-1 text-xs text-stone-500">
          {merchant.benefits.length > 0 && <span>{merchant.benefits.join(', ')}</span>}
          {cnpj && <span className="font-mono">{cnpj}</span>}
          {phone && (
            <a
              href={phone}
              className="text-stone-400 underline decoration-dotted hover:text-red-300 focus-visible:outline-2 focus-visible:outline-offset-2 focus-visible:outline-red-500"
            >
              ligar
            </a>
          )}
          <a
            href={walkUrl(merchant)}
            target="_blank"
            rel="noreferrer noopener"
            className="text-stone-400 underline decoration-dotted hover:text-red-300 focus-visible:outline-2 focus-visible:outline-offset-2 focus-visible:outline-red-500"
          >
            a pé
          </a>
        </div>
      </div>
      <span className="shrink-0 self-start rounded-lg bg-stone-900/70 px-2 py-1 font-mono text-xs text-stone-300">
        {formatDistance(merchant.distanciaMetros)}
      </span>
    </li>
  );
}

function ResultCard({ result }: { result: TargetResult }): ReactElement {
  const accepts = result.hits.length > 0;

  return (
    <article className="overflow-hidden rounded-2xl border border-white/10 bg-white/5 backdrop-blur-sm">
      <header className="flex items-center justify-between gap-3 px-4 py-3">
        <h3 className="truncate font-semibold tracking-tight text-stone-100">{result.term}</h3>
        {accepts ? (
          <span className="shrink-0 rounded-lg bg-emerald-400/15 px-2 py-1 text-xs font-semibold text-emerald-300">
            ACEITA
            {result.hits.length > 1 && ` (${result.hits.length})`}
          </span>
        ) : (
          <span className="shrink-0 rounded-lg bg-white/5 px-2 py-1 text-xs font-medium text-stone-400">
            não consta
          </span>
        )}
      </header>

      {accepts ? (
        <ul>
          {result.hits.map((hit) => (
            <HitRow key={`${hit.merchant.cnpj}-${hit.merchant.address}`} hit={hit} />
          ))}
        </ul>
      ) : (
        <p className="border-t border-white/5 px-4 py-3 text-sm text-stone-500">
          Nenhum credenciado com esse nome no alcance consultado.
        </p>
      )}
    </article>
  );
}

function formatHitsForClipboard(hits: MerchantHit[]): string {
  const header = ['Nome', 'Endereço', 'Benefícios', 'CNPJ', 'Contato', 'Distância'].join('\t');
  const rows = hits.map(({ merchant }) =>
    [
      merchant.fantasyName,
      merchant.address,
      merchant.benefits.join(', '),
      formatCnpj(merchant.cnpj) ?? merchant.cnpj,
      merchant.contact,
      formatDistance(merchant.distanciaMetros),
    ].join('\t'),
  );
  return [header, ...rows].join('\n');
}

function CopyHitsButton({ hits }: { hits: MerchantHit[] }): ReactElement {
  const [status, setStatus] = useState<'idle' | 'copied' | 'failed'>('idle');

  async function copy(): Promise<void> {
    if (hits.length === 0 || !navigator.clipboard?.writeText) {
      setStatus('failed');
      return;
    }

    try {
      await navigator.clipboard.writeText(formatHitsForClipboard(hits));
      setStatus('copied');
    } catch {
      setStatus('failed');
    }
  }

  useEffect(() => {
    if (status === 'idle') return;
    const timer = window.setTimeout(() => setStatus('idle'), 1_500);
    return () => window.clearTimeout(timer);
  }, [status]);

  const label =
    status === 'copied' ? 'Copiado' : status === 'failed' ? 'Falhou ao copiar' : 'Copiar tabela';

  return (
    <button
      type="button"
      onClick={() => void copy()}
      disabled={hits.length === 0}
      aria-label={label}
      title={label}
      className={`grid size-7 shrink-0 place-items-center rounded-lg border focus-visible:outline-2 focus-visible:outline-offset-2 focus-visible:outline-red-500 disabled:cursor-not-allowed disabled:opacity-40 disabled:hover:bg-transparent ${
        status === 'copied'
          ? 'border-emerald-400/30 text-emerald-300'
          : status === 'failed'
            ? 'border-red-400/30 text-red-300'
            : 'border-white/10 text-stone-300 hover:bg-white/5'
      }`}
    >
      {status === 'copied' ? (
        <svg aria-hidden="true" viewBox="0 0 24 24" className="size-3.5" fill="none">
          <path
            d="M5 13l4 4L19 7"
            stroke="currentColor"
            strokeWidth="2"
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        </svg>
      ) : status === 'failed' ? (
        <svg aria-hidden="true" viewBox="0 0 24 24" className="size-3.5" fill="none">
          <path
            d="M6 6l12 12M18 6L6 18"
            stroke="currentColor"
            strokeWidth="2"
            strokeLinecap="round"
          />
        </svg>
      ) : (
        <svg aria-hidden="true" viewBox="0 0 24 24" className="size-3.5" fill="none">
          <rect
            x="9"
            y="9"
            width="11"
            height="11"
            rx="2"
            stroke="currentColor"
            strokeWidth="2"
          />
          <path
            d="M5 15V5a2 2 0 0 1 2-2h10"
            stroke="currentColor"
            strokeWidth="2"
            strokeLinecap="round"
          />
        </svg>
      )}
    </button>
  );
}

function MerchantList({ hits }: { hits: MerchantHit[] }): ReactElement {
  return (
    <article className="overflow-hidden rounded-2xl border border-white/10 bg-white/5 backdrop-blur-sm">
      <header className="flex items-center justify-between gap-3 px-4 py-3">
        <h3 className="font-semibold tracking-tight text-stone-100">Credenciados por perto</h3>
        <div className="flex shrink-0 items-center gap-2">
          <span className="rounded-lg bg-white/5 px-2 py-1 font-mono text-xs text-stone-300">
            {hits.length}
          </span>
          <CopyHitsButton hits={hits} />
        </div>
      </header>

      {hits.length === 0 ? (
        <p className="border-t border-white/5 px-4 py-3 text-sm text-stone-500">
          Nenhum credenciado nesse raio com os benefícios escolhidos.
        </p>
      ) : (
        <ul>
          {hits.map((hit) => (
            <HitRow
              key={`${hit.merchant.cnpj}-${hit.merchant.address}-${hit.merchant.distanciaMetros}`}
              hit={hit}
            />
          ))}
        </ul>
      )}
    </article>
  );
}

function SweepBanner({ meta, radius }: { meta: SweepMeta; radius: number }): ReactElement {
  return (
    <div className="rounded-2xl border border-white/10 bg-white/5 px-4 py-3 text-sm backdrop-blur-sm">
      <p className="text-stone-300">
        <strong className="font-semibold text-stone-100">{meta.total}</strong> credenciados em
        memória, alcance real de{' '}
        <strong className="font-semibold text-stone-100">{formatDistance(meta.reach)}</strong>.
      </p>
      {meta.truncated && (
        <p className="mt-1.5 text-red-300">
          A varredura parou no limite de {MAX_PAGES} páginas, então pode haver credenciados entre{' '}
          {formatDistance(meta.reach)} e os {formatDistance(radius)} pedidos. Diminua o raio para
          cobrir tudo.
        </p>
      )}
    </div>
  );
}

function TargetsField({
  terms,
  onChange,
  disabled,
}: {
  terms: string[];
  onChange: (terms: string[]) => void;
  disabled: boolean;
}): ReactElement {
  const [draft, setDraft] = useState('');
  const full = terms.length >= MAX_TARGETS;

  function commit(raw: string): void {
    const term = raw.trim();
    if (!term) return;

    const exists = terms.some((current) => current.toUpperCase() === term.toUpperCase());
    if (!exists && terms.length < MAX_TARGETS) onChange([...terms, term]);
    setDraft('');
  }

  function onKeyDown(event: KeyboardEvent<HTMLInputElement>): void {
    if (event.key === 'Enter') {
      event.preventDefault();
      commit(draft);
      return;
    }
    if (event.key === 'Backspace' && draft === '' && terms.length > 0) {
      onChange(terms.slice(0, -1));
    }
  }

  return (
    <div>
      <label
        className="mb-1.5 block text-xs font-medium tracking-wide text-stone-400 uppercase"
        htmlFor="targets"
      >
        Estabelecimentos <span className="normal-case">(opcional)</span>
      </label>

      {terms.length > 0 && (
        <ul className="mb-2 flex flex-wrap gap-1.5">
          {terms.map((term) => (
            <li key={term.toUpperCase()}>
              <span className="inline-flex items-center gap-1 rounded-lg bg-red-500/20 py-1 pr-1 pl-2 text-xs font-medium text-red-300">
                {term}
                <button
                  type="button"
                  disabled={disabled}
                  onClick={() => onChange(terms.filter((current) => current !== term))}
                  className="rounded px-1 text-red-300/70 hover:bg-red-500/30 hover:text-stone-50 disabled:opacity-40"
                  aria-label={`remover ${term}`}
                >
                  x
                </button>
              </span>
            </li>
          ))}
        </ul>
      )}

      <input
        id="targets"
        className="w-full rounded-xl border border-white/10 bg-stone-900/60 px-3 py-2 text-sm text-stone-100 placeholder:text-stone-500 focus:border-red-500/60 focus-visible:outline-2 focus-visible:outline-offset-2 focus-visible:outline-red-500"
        value={draft}
        maxLength={MAX_TERM_LENGTH}
        disabled={disabled || full}
        placeholder={full ? `limite de ${MAX_TARGETS} termos` : 'MOLINO'}
        onChange={(event) => setDraft(event.target.value)}
        onKeyDown={onKeyDown}
        onBlur={() => commit(draft)}
        autoComplete="off"
        spellCheck={false}
      />
      <p className="mt-1.5 text-xs text-stone-500">
        Enter adiciona, até {MAX_TARGETS} termos. Vazio lista todos os credenciados do raio. Aceita
        expressão regular, por exemplo <code>MERCADO D[EO] CAFE</code>.
      </p>
    </div>
  );
}

interface FormState {
  lat: string;
  lon: string;
  radius: number;
  benefits: Benefit[];
}

interface GeocodeHit {
  displayName: string;
  lat: string;
  lon: string;
}

type GeoState = 'idle' | 'locating' | 'located' | 'denied' | 'unsupported' | 'address';

const GEO_MESSAGE: Record<GeoState, string> = {
  idle: 'Busque um endereço ou use sua localização.',
  locating: 'Buscando sua localização...',
  located: 'Centro na sua localização atual.',
  address: 'Centro pelo endereço escolhido.',
  denied: 'Localização indisponível. Busque um endereço acima.',
  unsupported: 'Este navegador não expõe geolocalização. Busque um endereço acima.',
};

async function searchAddress(query: string, signal: AbortSignal): Promise<GeocodeHit[]> {
  const url = new URL(NOMINATIM_URL);
  url.searchParams.set('format', 'json');
  url.searchParams.set('limit', '5');
  url.searchParams.set('countrycodes', 'br');
  url.searchParams.set('addressdetails', '0');
  url.searchParams.set('q', query);

  const response = await fetch(url, {
    signal,
    headers: { Accept: 'application/json' },
  });
  if (!response.ok) throw new Error('Falha ao buscar endereço.');

  const data: unknown = await response.json();
  if (!Array.isArray(data)) return [];

  return data.flatMap((item) => {
    if (
      typeof item !== 'object' ||
      item === null ||
      typeof (item as { display_name?: unknown }).display_name !== 'string' ||
      typeof (item as { lat?: unknown }).lat !== 'string' ||
      typeof (item as { lon?: unknown }).lon !== 'string'
    ) {
      return [];
    }
    const hit = item as { display_name: string; lat: string; lon: string };
    return [{ displayName: hit.display_name, lat: hit.lat, lon: hit.lon }];
  });
}

async function reverseAddress(
  latitude: number,
  longitude: number,
  signal: AbortSignal,
): Promise<string | null> {
  const url = new URL(NOMINATIM_REVERSE_URL);
  url.searchParams.set('format', 'json');
  url.searchParams.set('lat', String(latitude));
  url.searchParams.set('lon', String(longitude));
  url.searchParams.set('zoom', '18');
  url.searchParams.set('addressdetails', '0');

  const response = await fetch(url, {
    signal,
    headers: { Accept: 'application/json' },
  });
  if (!response.ok) throw new Error('Falha ao resolver endereço.');

  const data: unknown = await response.json();
  if (
    typeof data !== 'object' ||
    data === null ||
    typeof (data as { display_name?: unknown }).display_name !== 'string'
  ) {
    return null;
  }
  return (data as { display_name: string }).display_name;
}

interface AddressFill {
  id: number;
  label: string;
}

interface AddressFieldProps {
  disabled: boolean;
  fill: AddressFill | null;
  onPick: (hit: GeocodeHit) => void;
  onEdit: () => void;
  onClear: () => void;
}

function AddressField({ disabled, fill, onPick, onEdit, onClear }: AddressFieldProps): ReactElement {
  const listId = useId();
  const [query, setQuery] = useState('');
  const [hits, setHits] = useState<GeocodeHit[]>([]);
  const [open, setOpen] = useState(false);
  const [status, setStatus] = useState<'idle' | 'loading' | 'empty' | 'error'>('idle');
  const [active, setActive] = useState(-1);
  const abortRef = useRef<AbortController | null>(null);
  const timerRef = useRef<ReturnType<typeof setTimeout> | null>(null);
  const skipSearchRef = useRef(false);

  function commitLabel(label: string): void {
    skipSearchRef.current = true;
    setQuery(label);
    setHits([]);
    setOpen(false);
    setStatus('idle');
    setActive(-1);
  }

  function clear(): void {
    if (timerRef.current) clearTimeout(timerRef.current);
    abortRef.current?.abort();
    skipSearchRef.current = true;
    setQuery('');
    setHits([]);
    setOpen(false);
    setStatus('idle');
    setActive(-1);
    onClear();
  }

  useEffect(() => {
    if (!fill) return;
    commitLabel(fill.label);
  }, [fill]);

  useEffect(() => {
    if (skipSearchRef.current) {
      skipSearchRef.current = false;
      return;
    }

    if (timerRef.current) clearTimeout(timerRef.current);
    abortRef.current?.abort();

    const trimmed = query.trim();
    if (trimmed.length < GEOCODE_MIN_CHARS) {
      setHits([]);
      setOpen(false);
      setStatus('idle');
      setActive(-1);
      return;
    }

    setStatus('loading');
    timerRef.current = setTimeout(() => {
      const controller = new AbortController();
      abortRef.current = controller;
      void searchAddress(trimmed, controller.signal)
        .then((results) => {
          setHits(results);
          setOpen(true);
          setActive(results.length > 0 ? 0 : -1);
          setStatus(results.length > 0 ? 'idle' : 'empty');
        })
        .catch((error: unknown) => {
          if (error instanceof DOMException && error.name === 'AbortError') return;
          setHits([]);
          setOpen(false);
          setActive(-1);
          setStatus('error');
        });
    }, GEOCODE_DEBOUNCE_MS);

    return () => {
      if (timerRef.current) clearTimeout(timerRef.current);
      abortRef.current?.abort();
    };
  }, [query]);

  function pick(hit: GeocodeHit): void {
    commitLabel(hit.displayName);
    onPick(hit);
  }

  function onKeyDown(event: KeyboardEvent<HTMLInputElement>): void {
    if (event.key === 'ArrowDown' && hits.length > 0) {
      event.preventDefault();
      setOpen(true);
      setActive((current) => (current + 1) % hits.length);
      return;
    }
    if (event.key === 'ArrowUp' && hits.length > 0) {
      event.preventDefault();
      setOpen(true);
      setActive((current) => (current <= 0 ? hits.length - 1 : current - 1));
      return;
    }
    if (event.key === 'Enter' && open && active >= 0 && hits[active]) {
      event.preventDefault();
      pick(hits[active]);
      return;
    }
    if (event.key === 'Escape') {
      setOpen(false);
      setActive(-1);
    }
  }

  return (
    <div className="relative mb-2">
      <div className="relative">
        <input
          id="address"
          className={`w-full rounded-xl border border-white/10 bg-stone-900/60 py-2 pl-3 text-sm text-stone-100 placeholder:text-stone-500 focus:border-red-500/60 focus-visible:outline-2 focus-visible:outline-offset-2 focus-visible:outline-red-500 ${
            query ? 'pr-10' : 'pr-3'
          }`}
          value={query}
          disabled={disabled}
          placeholder="Rua, bairro, cidade..."
          aria-label="endereço"
          autoComplete="off"
          spellCheck={false}
          role="combobox"
          aria-expanded={open}
          aria-controls={listId}
          aria-autocomplete="list"
          aria-activedescendant={active >= 0 ? `${listId}-${active}` : undefined}
          onChange={(event) => {
            onEdit();
            setQuery(event.target.value);
          }}
          onKeyDown={onKeyDown}
          onBlur={() => {
            // Delay so a mousedown on a suggestion still registers.
            window.setTimeout(() => setOpen(false), 120);
          }}
          onFocus={() => {
            if (hits.length > 0) setOpen(true);
          }}
        />
        {query !== '' && (
          <button
            type="button"
            disabled={disabled}
            onMouseDown={(event) => event.preventDefault()}
            onClick={clear}
            aria-label="limpar endereço"
            className="absolute top-1/2 right-2 grid size-7 -translate-y-1/2 place-items-center rounded-lg text-stone-400 hover:bg-white/10 hover:text-stone-100 focus-visible:outline-2 focus-visible:outline-offset-2 focus-visible:outline-red-500 disabled:opacity-40"
          >
            <span aria-hidden="true" className="text-base leading-none">
              ×
            </span>
          </button>
        )}
      </div>
      {open && hits.length > 0 && (
        <ul
          id={listId}
          role="listbox"
          className="absolute z-10 mt-1 max-h-56 w-full overflow-auto rounded-xl border border-white/10 bg-stone-900 py-1 shadow-lg"
        >
          {hits.map((hit, index) => (
            <li key={`${hit.lat},${hit.lon},${hit.displayName}`} role="option" aria-selected={index === active}>
              <button
                id={`${listId}-${index}`}
                type="button"
                className={`block w-full px-3 py-2 text-left text-sm ${
                  index === active
                    ? 'bg-red-500/20 text-stone-50'
                    : 'text-stone-300 hover:bg-white/5'
                }`}
                onMouseDown={(event) => event.preventDefault()}
                onMouseEnter={() => setActive(index)}
                onClick={() => pick(hit)}
              >
                {hit.displayName}
              </button>
            </li>
          ))}
        </ul>
      )}
      <p className="mt-1.5 text-xs text-stone-500">
        {status === 'loading' && 'Buscando endereços...'}
        {status === 'empty' && 'Nenhum endereço encontrado.'}
        {status === 'error' && 'Não foi possível buscar o endereço agora.'}
        {status === 'idle' &&
          query.trim().length < GEOCODE_MIN_CHARS &&
          'Digite pelo menos 3 caracteres e escolha uma sugestão.'}
      </p>
    </div>
  );
}

interface SearchPanelProps {
  form: FormState;
  terms: string[];
  loading: boolean;
  onFormChange: (patch: Partial<FormState>) => void;
  onTermsChange: (terms: string[]) => void;
  onSubmit: () => void;
  onCancel: () => void;
}

function SearchPanel({
  form,
  terms,
  loading,
  onFormChange,
  onTermsChange,
  onSubmit,
  onCancel,
}: SearchPanelProps): ReactElement {
  const [geoState, setGeoState] = useState<GeoState>(() =>
    'geolocation' in navigator ? 'locating' : 'unsupported',
  );
  const [addressFill, setAddressFill] = useState<AddressFill | null>(null);
  const locateSeq = useRef(0);
  const reverseAbort = useRef<AbortController | null>(null);
  const calls = plannedRequests(terms);
  const inMemory = terms.length === 0 || terms.some(looksLikeRegex);

  const locate = useCallback(() => {
    const seq = ++locateSeq.current;
    reverseAbort.current?.abort();
    const controller = new AbortController();
    reverseAbort.current = controller;

    navigator.geolocation.getCurrentPosition(
      (position) => {
        if (seq !== locateSeq.current) return;

        const latitude = position.coords.latitude;
        const longitude = position.coords.longitude;
        onFormChange({
          lat: latitude.toFixed(5),
          lon: longitude.toFixed(5),
        });
        setGeoState('located');

        void reverseAddress(latitude, longitude, controller.signal)
          .then((label) => {
            if (seq !== locateSeq.current || !label) return;
            setAddressFill({ id: seq, label });
          })
          .catch((error: unknown) => {
            if (error instanceof DOMException && error.name === 'AbortError') return;
          });
      },
      () => {
        if (seq !== locateSeq.current) return;
        setGeoState('denied');
      },
      { timeout: 10_000, maximumAge: 60_000 },
    );
  }, [onFormChange]);

  useEffect(() => {
    if ('geolocation' in navigator) locate();
    return () => {
      locateSeq.current += 1;
      reverseAbort.current?.abort();
    };
  }, [locate]);

  function retryLocation(): void {
    setGeoState('locating');
    locate();
  }

  function pickAddress(hit: GeocodeHit): void {
    locateSeq.current += 1;
    reverseAbort.current?.abort();
    onFormChange({
      lat: Number(hit.lat).toFixed(5),
      lon: Number(hit.lon).toFixed(5),
    });
    setGeoState('address');
  }

  function editAddress(): void {
    if (geoState === 'located') setGeoState('address');
  }

  function clearAddress(): void {
    locateSeq.current += 1;
    reverseAbort.current?.abort();
    setAddressFill(null);
    onFormChange({ lat: '', lon: '' });
    setGeoState('geolocation' in navigator ? 'idle' : 'unsupported');
  }

  const usingLocation = geoState === 'located' || geoState === 'locating';

  return (
    <form
      className="flex flex-col gap-5 rounded-2xl border border-white/10 bg-white/5 p-5 backdrop-blur-sm"
      onSubmit={(event) => {
        event.preventDefault();
        onSubmit();
      }}
    >
      <fieldset disabled={loading} className="contents">
        <TargetsField terms={terms} onChange={onTermsChange} disabled={loading} />

        <div>
          <span className="mb-1.5 block text-xs font-medium tracking-wide text-stone-400 uppercase">
            Centro da busca
          </span>
          <AddressField
            disabled={loading}
            fill={addressFill}
            onPick={pickAddress}
            onEdit={editAddress}
            onClear={clearAddress}
          />
          <div className="mt-2 flex flex-wrap items-center gap-2">
            <button
              type="button"
              onClick={retryLocation}
              disabled={geoState === 'locating' || geoState === 'unsupported'}
              aria-pressed={geoState === 'located'}
              className={`rounded-lg border px-2.5 py-1 text-xs font-medium transition focus-visible:outline-2 focus-visible:outline-offset-2 focus-visible:outline-red-500 disabled:cursor-not-allowed disabled:opacity-40 disabled:hover:bg-transparent ${
                usingLocation
                  ? 'border-red-500/60 bg-red-500/20 text-red-300'
                  : 'border-white/10 text-stone-300 hover:bg-white/5'
              }`}
            >
              {geoState === 'locating'
                ? 'Localizando...'
                : geoState === 'located'
                  ? 'Usando minha localização'
                  : 'Usar minha localização'}
            </button>
          </div>
          <p
            className={`mt-1.5 text-xs ${
              geoState === 'denied' || geoState === 'unsupported'
                ? 'text-red-300'
                : 'text-stone-500'
            }`}
          >
            {GEO_MESSAGE[geoState]}
          </p>
        </div>

        <div>
          <label
            className="mb-1.5 block text-xs font-medium tracking-wide text-stone-400 uppercase"
            htmlFor="radius"
          >
            Raio: {(form.radius / 1000).toFixed(1).replace('.', ',')} km
          </label>
          <input
            id="radius"
            type="range"
            min={500}
            max={MAX_RADIUS}
            step={500}
            value={form.radius}
            onChange={(event) => onFormChange({ radius: Number(event.target.value) })}
            className="w-full accent-red-500 focus-visible:outline-2 focus-visible:outline-offset-2 focus-visible:outline-red-500"
          />
        </div>

        <div>
          <span className="mb-1.5 block text-xs font-medium tracking-wide text-stone-400 uppercase">
            Benefícios
          </span>
          <div className="flex flex-wrap gap-1.5">
            {BENEFITS.map((benefit) => {
              const active = form.benefits.includes(benefit);
              return (
                <button
                  key={benefit}
                  type="button"
                  aria-pressed={active}
                  onClick={() =>
                    onFormChange({
                      benefits: active
                        ? form.benefits.filter((current) => current !== benefit)
                        : [...form.benefits, benefit],
                    })
                  }
                  className={`rounded-lg border px-2.5 py-1 text-xs font-medium transition focus-visible:outline-2 focus-visible:outline-offset-2 focus-visible:outline-red-500 ${
                    active
                      ? 'border-red-500/60 bg-red-500/20 text-red-300'
                      : 'border-white/10 text-stone-400 hover:bg-white/5'
                  }`}
                >
                  {BENEFIT_LABEL[benefit]}
                </button>
              );
            })}
          </div>
        </div>
      </fieldset>

      {loading ? (
        <button
          type="button"
          onClick={onCancel}
          className="rounded-xl border border-white/15 px-4 py-2.5 text-sm font-semibold text-stone-200 hover:bg-white/5 focus-visible:outline-2 focus-visible:outline-offset-2 focus-visible:outline-red-500"
        >
          Cancelar consulta
        </button>
      ) : (
        <div>
          <button
            type="submit"
            className="w-full rounded-xl bg-red-600 px-4 py-2.5 text-sm font-semibold text-white transition hover:bg-red-500 focus-visible:outline-2 focus-visible:outline-offset-2 focus-visible:outline-red-500 disabled:cursor-not-allowed disabled:opacity-40 disabled:hover:bg-red-600"
          >
            {terms.length === 0 ? 'Listar credenciados por perto' : 'Consultar rede credenciada'}
          </button>
          <p className="mt-1.5 text-center text-xs text-stone-500">
            {calls === 1 ? 'no mínimo 1 consulta' : `no mínimo ${calls} consultas`}
            {inMemory ? ', filtradas em memória' : ', filtradas no servidor'}
            {', cada uma paginada até o fim do raio'}
          </p>
        </div>
      )}
    </form>
  );
}

interface Search {
  params: SearchParams;
  terms: string[];
}

const queryClient = new QueryClient({
  defaultOptions: {
    queries: {
      retry: false,
      staleTime: 5 * 60_000,
      gcTime: 30 * 60_000,
      refetchOnWindowFocus: false,
    },
  },
});

const INITIAL_FORM: FormState = {
  lat: '',
  lon: '',
  radius: DEFAULT_RADIUS,
  benefits: ['RESTAURANTE'],
};

function parseCoordinate(raw: string): number {
  return Number(raw.trim().replace(',', '.'));
}

function describeError(error: unknown): string {
  if (error instanceof ApiError || error instanceof PatternError) return error.message;
  if (error instanceof InvalidParamsError) return error.message;
  return 'Falha inesperada ao consultar a rede credenciada.';
}

function SearchPage(): ReactElement {
  const [form, setForm] = useState<FormState>(INITIAL_FORM);
  const [terms, setTerms] = useState<string[]>([]);

  const [search, setSearch] = useState<Search | null>(null);
  const [formError, setFormError] = useState('');
  const [progress, setProgress] = useState<SearchProgress>({ done: 0, total: 0, page: 0 });

  const client = useQueryClient();
  const query = useQuery({
    queryKey: ['merchants', search],
    queryFn: search
      ? ({ signal }: { signal: AbortSignal }): Promise<SearchOutcome> =>
          runSearch({
            params: search.params,
            terms: search.terms,
            signal,
            onProgress: setProgress,
          })
      : skipToken,
  });

  const outcome = query.data ?? null;
  const loading = query.isFetching;
  const error = formError || (query.isError ? describeError(query.error) : '');
  const accepted = outcome?.results.filter((item) => item.hits.length > 0).length ?? 0;

  const patchForm = useCallback((patch: Partial<FormState>): void => {
    setForm((current) => ({ ...current, ...patch }));
  }, []);

  function cancel(): void {
    void client.cancelQueries({ queryKey: ['merchants', search], exact: true });
  }

  function submit(): void {
    const latitude = parseCoordinate(form.lat);
    const longitude = parseCoordinate(form.lon);
    if (!Number.isFinite(latitude) || !Number.isFinite(longitude)) {
      setFormError('Escolha um endereço ou use sua localização.');
      return;
    }

    const next: Search = {
      params: { latitude, longitude, radius: form.radius, benefits: form.benefits },
      terms: cleanTerms(terms),
    };

    setFormError('');
    setProgress({ done: 0, total: plannedRequests(terms), page: 0 });

    if (hashKey(['merchants', next]) === hashKey(['merchants', search])) {
      void query.refetch();
      return;
    }
    setSearch(next);
  }

  return (
    <div className="mx-auto max-w-6xl px-4 py-8 sm:px-6 lg:py-12">
      <div
        aria-hidden="true"
        className="pointer-events-none fixed inset-0 -z-10 bg-radial-[at_12%_0%] from-red-500/20 to-transparent to-60%"
      />
      <div
        aria-hidden="true"
        className="pointer-events-none fixed inset-0 -z-10 bg-radial-[at_95%_0%] from-red-800/25 to-transparent to-45%"
      />

      <header className="mb-8 flex items-start gap-3">
        <span
          aria-hidden="true"
          className="mt-0.5 grid size-10 shrink-0 place-items-center rounded-xl bg-red-500 font-bold text-white"
        >
          T
        </span>
        <div>
          <h1 className="text-2xl font-semibold tracking-tight text-stone-50 sm:text-3xl">
            Onde aceita Ticket
          </h1>
          <p className="text-sm text-stone-400">
            Consulta a rede credenciada da Edenred e diz quem aceita o benefício.
          </p>
        </div>
      </header>

      <div className="grid items-start gap-6 lg:grid-cols-[22rem_1fr]">
        <div className="lg:sticky lg:top-8">
          <SearchPanel
            form={form}
            terms={terms}
            loading={loading}
            onFormChange={patchForm}
            onTermsChange={setTerms}
            onSubmit={submit}
            onCancel={cancel}
          />
        </div>

        <main className="flex flex-col gap-4">
          {error && (
            <p
              className="rounded-2xl border border-red-400/25 bg-red-400/10 px-4 py-3 text-sm text-red-200 backdrop-blur-sm"
              role="alert"
            >
              {error}
            </p>
          )}

          {loading && (
            <div className="rounded-2xl border border-white/10 bg-white/5 px-4 py-3 text-sm text-stone-300 backdrop-blur-sm">
              {progress.total > 1
                ? `Consultando ${Math.min(progress.done + 1, progress.total)} de ${progress.total} termos`
                : 'Baixando credenciados ao redor do ponto'}
              {progress.page > 1 && `, página ${progress.page}`}...
              <div className="mt-2 h-1 overflow-hidden rounded-full bg-white/10">
                <div
                  className="h-full rounded-full bg-red-500 transition-all"
                  style={{
                    width: `${progress.total > 0 ? (progress.done / progress.total) * 100 : 8}%`,
                  }}
                />
              </div>
            </div>
          )}

          {outcome && !loading && (
            <>
              {outcome.sweep && <SweepBanner meta={outcome.sweep} radius={form.radius} />}

              {outcome.listing ? (
                <MerchantList hits={outcome.listing} />
              ) : (
                <>
                  <p className="px-1 text-sm text-stone-400">
                    {accepted} de {outcome.results.length}{' '}
                    {outcome.results.length === 1 ? 'termo aceita' : 'termos aceitam'} o benefício.
                  </p>
                  {outcome.results.map((result) => (
                    <ResultCard key={result.term.toUpperCase()} result={result} />
                  ))}
                </>
              )}
            </>
          )}

          {!outcome && !loading && !error && (
            <section className="rounded-2xl border border-white/10 bg-white/5 px-5 py-6 text-sm text-stone-400 backdrop-blur-sm">
              <h2 className="mb-2 font-semibold text-stone-200">Como usar</h2>
              <ul className="flex list-disc flex-col gap-1.5 pl-4">
                <li>
                  Informar nome é opcional. Sem nenhum termo, a varredura lista todos os
                  credenciados ao redor do ponto, do mais perto ao mais longe.
                </li>
                <li>
                  Cada nome vira uma consulta filtrada no servidor da Ticket, que cobre o raio
                  inteiro. É a forma confiável de dizer se um lugar aceita ou não.
                </li>
                <li>
                  Todo termo pode ser expressão regular. Com metacaractere, como{' '}
                  <code>MERCADO D[EO] CAFE</code>, o filtro roda em memória sobre a varredura. A API
                  entrega no máximo 1000 credenciados por página, então percorremos as páginas até
                  acabar, o que em região densa custa várias chamadas seguidas.
                </li>
                <li>
                  A comparação ignora acento e maiúscula. Termo sem metacaractere ancora no início
                  da palavra: ILLA não casa dentro de VILLA, mas TAPIOQUEIRA ainda casa em
                  TAPIOQUEIRAS.
                </li>
              </ul>
            </section>
          )}
        </main>
      </div>

      <footer className="mt-10 text-xs text-stone-600">
        Dados da rede credenciada Ticket (Edenred), consultados direto do navegador. Projeto sem
        vínculo com a Edenred.
      </footer>
    </div>
  );
}

export default function App(): ReactElement {
  return (
    <QueryClientProvider client={queryClient}>
      <SearchPage />
    </QueryClientProvider>
  );
}
