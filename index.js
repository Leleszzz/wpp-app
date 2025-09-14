// index.js — WhatsApp Expenses Agent (wwebjs + OpenAI + MongoDB + Luxon)
// Recursos principais:
// - Lançamentos simples e múltiplos ("paiol 16 e monster 11")
// - Categoria padrão "Diversos" quando não identificar
// - Listar lançamentos individuais por categoria (dos dois por padrão; filtra pagador só se pedido)
// - Edição por mensagem: mover categoria, alterar valor, apagar (#n, short id 6, ou ObjectId)
// - Memória da última listagem por chat (#n) com TTL configurável
// - **Padrão de período:** SEMPRE o mês atual, a menos que a mensagem peça explicitamente "mês passado"/"mês anterior" ou "anual/este ano"
//
// Dependências:
//   npm i whatsapp-web.js qrcode-terminal mongodb openai dotenv luxon
//
// .env (exemplo):
//   OPENAI_API_KEY=sk-xxx
//   OPENAI_MODEL=gpt-4o-mini
//   MONGODB_URI=mongodb+srv://usuario:senha@host/db
//   MONGODB_DB=wpp_expenses
//   ALLOW_ALL_GROUPS=true
//   GROUP_ID=        # opcional, se quiser travar a um grupo específico
//   MY_WPP_ID=5531999999999
//   SPOUSE_WPP_ID=5531888888888
//   TZ=America/Sao_Paulo
//   LASTLIST_TTL_MS=1800000

require('dotenv').config();
const { Client, LocalAuth } = require('whatsapp-web.js');
const qrcode = require('qrcode-terminal');
const { MongoClient, ObjectId } = require('mongodb');
const OpenAI = require('openai');
const { DateTime } = require('luxon');

// ========================= CONFIG =========================
const OPENAI_MODEL = process.env.OPENAI_MODEL || 'gpt-4o-mini';
const ALLOW_ALL_GROUPS = process.env.ALLOW_ALL_GROUPS === 'true';
const GROUP_ID = process.env.GROUP_ID || '';
const ME = (process.env.MY_WPP_ID || '').replace(/\D/g, '');
const SPOUSE = (process.env.SPOUSE_WPP_ID || '').replace(/\D/g, '');
const TZ = process.env.TZ || 'America/Sao_Paulo';
const LASTLIST_TTL_MS = parseInt(process.env.LASTLIST_TTL_MS || '1800000', 10); // 30min

// ==========================================================
const wpp = new Client({
  authStrategy: new LocalAuth({
    clientId: 'expenses-bot',
    dataPath: process.env.WWEB_DATA_PATH || './.wwebjs_auth'
  }),
  puppeteer: {
    headless: true,
    executablePath: process.env.PUPPETEER_EXECUTABLE_PATH || '/usr/bin/chromium',
    args: ['--no-sandbox','--disable-setuid-sandbox','--disable-dev-shm-usage']
  }
});


const openai = new OpenAI({ apiKey: process.env.OPENAI_API_KEY });
const mongo = new MongoClient(process.env.MONGODB_URI, { maxPoolSize: 10 });

let db, Expenses;

// ========================= TIME HELPERS (Luxon c/ TZ) =========================
const now = () => DateTime.now().setZone(TZ);
const startOfMonth = (dt = now()) => dt.startOf('month');
const endOfMonth = (dt = now()) => dt.plus({ months: 1 }).startOf('month'); // exclusivo
const startOfToday = (dt = now()) => dt.startOf('day');
const startOfYesterday = (dt = now()) => dt.minus({ days: 1 }).startOf('day');
const endOfYesterday = (dt = now()) => dt.startOf('day');
const startOfWeek = (dt = now()) => dt.set({ weekday: 1 }).startOf('day'); // segunda
const toJSDate = (dt) => dt.toJSDate();
const fmtBR = (dt) => dt.setZone(TZ).toFormat('dd/LL/yyyy');
const fmtHour = (dt) => dt.setZone(TZ).toFormat('HH:mm');

// ========================= FORMAT/UTILS =========================
function brl(n) {
  try { return n.toLocaleString('pt-BR', { style: 'currency', currency: 'BRL', timeZone: 'UTC' }); }
  catch { return `R$ ${n}`; }
}
function normalizeAmount(txt) {
  if (typeof txt === 'number') return txt;
  if (!txt) return null;
  let s = String(txt).trim();
  s = s.replace(/\s|R\$|\u00A0/gi, '');
  if (/\d+\.\d{3},\d{2}$/.test(s) || /\d{1,3}(\.\d{3})+,\d{2}$/.test(s)) {
    s = s.replace(/\./g, '').replace(/,/g, '.');
  } else if (/^\d+,\d{1,2}$/.test(s)) {
    s = s.replace(/,/g, '.');
  }
  const n = parseFloat(s);
  return Number.isFinite(n) ? n : null;
}
function escapeRegex(s) { return s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'); }
function safeParseJSON(s) {
  if (!s) return null;
  let t = String(s).trim().replace(/```json|```/gi, '').trim();
  const first = t.indexOf('{'), last = t.lastIndexOf('}');
  if (first >= 0 && last > first) t = t.slice(first, last + 1);
  try { return JSON.parse(t); } catch { return null; }
}
const normalizeTxt = (t) =>
  (t || '').toLowerCase().normalize('NFD').replace(/\p{Diacritic}/gu, '');

// ---------- Categorias & sinônimos ----------
const CANONICAL_CATS = new Set([
  'Paiol/cigarro', 'Maconha', 'Energeticos', 'Bebidas alcoólicas', 'Ifood', 'Jogos',
  'transporte/uber', 'transporte/combustivel', 'transporte', 'mercado', 'saude/farmacia',
  'Diversos'
]);

const CAT_SYNONYMS = {
  // novas
  'paiol': 'Paiol/cigarro', 'cigarro': 'Paiol/cigarro', 'cigarros': 'Paiol/cigarro', 'tabaco': 'Paiol/cigarro',
  'maconha': 'Maconha', 'erva': 'Maconha', 'ganja': 'Maconha', 'beck': 'Maconha',
  'monster': 'Energeticos', 'redbull': 'Energeticos', 'red bull': 'Energeticos',
  'energetico': 'Energeticos', 'energeticos': 'Energeticos',
  'cerveja': 'Bebidas alcoólicas', 'vodka': 'Bebidas alcoólicas', 'vinho': 'Bebidas alcoólicas',
  'whisky': 'Bebidas alcoólicas', 'cachaca': 'Bebidas alcoólicas', 'cachaça': 'Bebidas alcoólicas',
  'pinga': 'Bebidas alcoólicas', 'bebida': 'Bebidas alcoólicas', 'bebidas': 'Bebidas alcoólicas',
  'alcool': 'Bebidas alcoólicas', 'álcool': 'Bebidas alcoólicas',
  'ifood': 'Ifood', 'i-food': 'Ifood',
  'jogo': 'Jogos', 'jogos': 'Jogos', 'steam': 'Jogos', 'psn': 'Jogos', 'xbox': 'Jogos', 'game pass': 'Jogos',

  // existentes
  'uber': 'transporte/uber', '99': 'transporte/uber',
  'mercado': 'mercado',
  'gasolina': 'transporte/combustivel', 'gasolinao': 'transporte/combustivel', 'combustivel': 'transporte/combustivel',
  'farmacia': 'saude/farmacia', 'remedio': 'saude/farmacia', 'remedios': 'saude/farmacia', 'remédios': 'saude/farmacia',

  // fallback explícito
  'diversos': 'Diversos', 'outros': 'Diversos', 'misc': 'Diversos',
};

function unifyCategory(raw) {
  if (!raw) return null;
  const k = normalizeTxt(raw).trim();
  return CAT_SYNONYMS[k] || raw; // mantém como veio se não mapeado
}
function ensureCategory(cat) {
  const c = unifyCategory(cat) || 'Diversos';
  return CANONICAL_CATS.has(c) ? c : 'Diversos';
}
function payerFromAuthorId(authorId) {
  if (!authorId) return null;
  const num = String(authorId).split('@')[0].replace(/\D/g, '');
  if (num === ME) return 'matheus';
  if (num === SPOUSE) return 'esposa';
  return 'desconhecido';
}

// ========================= Períodos por TEXTO =========================
// Regra: padrão = mês atual. Detecta exceções: "mês passado"/"mês anterior" e "anual/este ano/ano"
function getPeriodFromText(text) {
  if (!text) return null;
  const s = normalizeTxt(text);
  const n = now();

  // mês atual (explícito)
  if (/\beste mes\b|\bneste mes\b|\bnesse mes\b|\bmes atual\b/.test(s)) {
    return { start: toJSDate(startOfMonth(n)), end: toJSDate(endOfMonth(n)), label: 'este mês' };
  }
  // mês passado / mês anterior / último mês
  if (/\bmes passado\b|\bmes anterior\b|\bultimo mes\b|\bultimo mês\b/.test(s)) {
    const prev = n.minus({ months: 1 });
    return { start: toJSDate(startOfMonth(prev)), end: toJSDate(endOfMonth(prev)), label: 'mês passado' };
  }
  // anual / este ano / no ano / ano atual
  if (/\banual\b|\beste ano\b|\bano atual\b|\bno ano\b|\bano todo\b/.test(s)) {
    const st = n.startOf('year');
    return { start: toJSDate(st), end: toJSDate(st.plus({ years: 1 })), label: 'este ano' };
  }
  // ano passado (mantido)
  if (/\bano passado\b/.test(s)) {
    const st = n.minus({ years: 1 }).startOf('year');
    return { start: toJSDate(st), end: toJSDate(st.plus({ years: 1 })), label: 'ano passado' };
  }
  // hoje/ontem/semana (mantido)
  if (/\bhoje\b/.test(s)) {
    const st = startOfToday(n);
    return { start: toJSDate(st), end: toJSDate(st.plus({ days: 1 })), label: 'hoje' };
  }
  if (/\bontem\b/.test(s)) {
    return { start: toJSDate(startOfYesterday(n)), end: toJSDate(endOfYesterday(n)), label: 'ontem' };
  }
  if (/\besta semana\b|\bsemana atual\b/.test(s)) {
    const st = startOfWeek(n);
    return { start: toJSDate(st), end: toJSDate(st.plus({ days: 7 })), label: 'esta semana' };
  }
  if (/\bsemana passada\b/.test(s)) {
    const st = startOfWeek(n.minus({ weeks: 1 }));
    return { start: toJSDate(st), end: toJSDate(st.plus({ days: 7 })), label: 'semana passada' };
  }
  return null;
}

// ========================= Extração de intenção LISTA por categoria =========================
function findCategoryInText(text) {
  const s = normalizeTxt(text);
  const keys = Object.keys(CAT_SYNONYMS).sort((a, b) => b.length - a.length);
  for (const k of keys) {
    const re = new RegExp(`\\b${escapeRegex(k)}\\b`, 'i');
    if (re.test(s)) return CAT_SYNONYMS[k];
  }
  return null;
}
// Aceita "listar", "liste", "lista", "mostrar", "mostra", "me liste", "me mostra", etc.
function isListRequest(text) {
  const s = normalizeTxt(text);
  const verb = /\b(mostrar|mostra|listar|liste|lista|me\s+mostra|me\s+liste|me\s+lista|todos(?:\s+os)?|todas(?:\s+as)?)\b/.test(s);
  const noun = /\b(gasto|gastos|lancamento|lançamentos)\b/.test(s);
  return verb && noun;
}
// Filtra pagador só quando for explicitamente pedido; padrão = dos dois
function getExplicitPayerFilter(text, senderPayer) {
  const s = normalizeTxt(text);
  if (/\bda esposa\b|\bda minha esposa\b|\bda mulher\b|\bdela\b/.test(s)) return 'esposa';
  if (/\bdo matheus\b|\bdo mateus\b/.test(s)) return 'matheus';
  if (/\bmeus\b|\bmeu\b/.test(s)) return senderPayer || 'desconhecido';
  return null;
}

// ========================= PARSE DE LANÇAMENTOS =========================
function parseSingleRecord(text) {
  const m = String(text).trim().match(/^(?<cat>[\p{L}][\p{L}\s\-_\/]{0,30})\s*[:\- ]*\$?(?<val>-?\d+(?:[.,]\d{1,2})?)/iu);
  if (!m) return null;
  const amount = normalizeAmount(m.groups.val);
  const category = ensureCategory(m.groups.cat.trim());
  if (!amount || !category) return null;
  return { category, amount };
}
function parseMultipleRecords(text) {
  if (!text) return [];
  const chunks = String(text).replace(/\s{2,}/g, ' ').split(/\s+(?:e|&|\+)\s+|[,;]+/i).map(s => s.trim()).filter(Boolean);
  const items = [];
  for (const ch of chunks) {
    const rec = parseSingleRecord(ch);
    if (rec) items.push(rec);
  }
  return items;
}

// ========================= OPENAI CLASSIFIER =========================
const SYSTEM_ANALYZER = `
Você é um parser de mensagens financeiras em português do Brasil.
Converta a mensagem em um JSON ESTRITO e VÁLIDO no formato:
{
  "action": "record" | "query" | "other",
  "amount": number|null,
  "currency": "BRL",
  "category": string|null,
  "notes": string|null,
  "date": string|null,
  "filters": {
    "category": string|null,
    "payer": "matheus"|"esposa"|null,
    "start": string|null,
    "end": string|null
  }
}
REGRAS:
- Para lançamentos do tipo "uber 29" ou "paiol 16 e monster 11", use action="record". (Se houver múltiplos itens, o bot divide por conta própria.)
- Para perguntas do tipo "quanto gastei com <categoria> este mês?", use action="query".
- Responda SOMENTE com JSON válido, sem explicações.
`.trim();

async function analyzeWithGPT(messageText, context) {
  const hints = { payer_hint: context?.payer || null };
  try {
    const resp = await openai.chat.completions.create({
      model: OPENAI_MODEL,
      temperature: 0,
      messages: [
        { role: 'system', content: SYSTEM_ANALYZER },
        { role: 'user', content: JSON.stringify({ text: messageText, hints }) },
      ],
    });
    const raw = resp.choices?.[0]?.message?.content || '';
    const parsed = safeParseJSON(raw);
    if (parsed) return parsed;
  } catch {}
  return { action: 'other' };
}

// ========================= LISTAGEM/EDIÇÃO =========================
// Memória: chatId -> { ts, docs }
const lastLists = new Map();
function setLastList(chatId, docs) { lastLists.set(chatId, { ts: Date.now(), docs }); }
function getLastList(chatId) {
  const entry = lastLists.get(chatId);
  if (!entry) return null;
  if (Date.now() - entry.ts > LASTLIST_TTL_MS) { lastLists.delete(chatId); return null; }
  return entry.docs;
}
function idHex(objId) { try { return new ObjectId(objId).toHexString(); } catch { return null; } }
function last6(objId) { const h = typeof objId === 'string' ? objId : idHex(objId); return h ? h.slice(-6).toLowerCase() : null; }

// Resolve #n, short id (6) ou ObjectId
function resolveRefToId(chatId, ref) {
  if (!ref) return null;
  if (/^#\d+$/.test(ref)) {
    const idx = parseInt(ref.slice(1), 10) - 1;
    const arr = getLastList(chatId) || [];
    const doc = arr[idx];
    return doc?._id ? String(doc._id) : null;
  }
  if (/^[a-f0-9]{6}$/i.test(ref)) {
    const arr = getLastList(chatId) || [];
    const doc = arr.find(d => last6(d._id) === ref.toLowerCase());
    return doc?._id ? String(doc._id) : null;
  }
  if (/^[a-f0-9]{24}$/i.test(ref)) return ref;
  return null;
}

async function handleListByCategory(msg, cat, explicitPayer, text) {
  // Sempre aplicar período: padrão mês atual, exceto se especificado "mês passado"/"anual"/etc.
  const p = getPeriodFromText(text);
  let start = p?.start, end = p?.end, label = p?.label;
  if (!start || !end) { start = toJSDate(startOfMonth()); end = toJSDate(endOfMonth()); label = 'este mês'; }

  const q = {
    chatId: msg.from,
    category: { $regex: new RegExp(`^${escapeRegex(cat)}$`, 'i') },
    timestamp: { $gte: start, $lt: end },
  };
  if (explicitPayer) q.payer = explicitPayer;

  const LIMIT = 200;
  const docs = await Expenses.find(q).sort({ timestamp: -1 }).limit(LIMIT).toArray();
  setLastList(msg.from, docs);

  if (docs.length === 0) {
    const who = explicitPayer ? ` (${explicitPayer})` : '';
    await msg.reply(`Não encontrei lançamentos em *${cat}*${who} (${label}).`);
    return;
  }

  const total = docs.reduce((s, d) => s + (d.amount || 0), 0);
  const lines = docs.map((d, i) => {
    const dt = DateTime.fromJSDate(d.timestamp).setZone(TZ);
    const sid = last6(d._id);
    const payer = d.payer || '—';
    return `[#${i + 1}] ${fmtBR(dt)} ${fmtHour(dt)} | ${brl(d.amount)} | ${payer} | id:${sid}`;
  });

  const header =
    `🧾 ${docs.length} lançamento(s) em *${cat}*` +
    (explicitPayer ? ` (${explicitPayer})` : '') +
    ` • Total: *${brl(total)}* • (${label})`;
  const help =
    `\n\nAções:\n` +
    `- Mover:   mover #2 para transportes\n` +
    `- Alterar: alterar #2 para 12,90\n` +
    `- Apagar:  apagar #1\n` +
    `- Também aceita short id (6): apagar c67f04`;

  const chunks = [];
  let buf = header + '\n' + lines[0];
  for (let i = 1; i < lines.length; i++) {
    if ((buf + '\n' + lines[i]).length > 3000) { chunks.push(buf); buf = lines[i]; }
    else { buf += '\n' + lines[i]; }
  }
  chunks.push(buf + help);

  for (const c of chunks) {
    // eslint-disable-next-line no-await-in-loop
    await msg.reply(c);
  }
}

function parseAdminCommand(text) {
  if (!text) return null;
  const s = text.toLowerCase();

  // LISTAR DIVERSOS rápido
  if (/(mostrar|mostra|listar|liste|lista|todos|todas).*(gastos?).*(diversos|outros|misc)/i.test(text)) {
    return { cmd: 'listByCat', cat: 'Diversos' };
  }

  // MOVER CATEGORIA
  let m = s.match(/\b(?:mover|mudar|trocar|colocar)\s+(#\d+|id\s+[a-f0-9]{24}|[a-f0-9]{24}|[a-f0-9]{6})\s+(?:para|pra)\s+(.+)$/i);
  if (m) {
    const ref = m[1].replace(/^id\s+/i, '').trim();
    const newCat = m[2].trim();
    return { cmd: 'changeCategory', ref, newCat };
  }
  m = s.match(/gasto\s+(#\d+)\b.*(?:categoria|para)\s+(.+)$/i);
  if (m) return { cmd: 'changeCategory', ref: m[1], newCat: m[2].trim() };

  // ALTERAR VALOR — aceita "valor X", "para X", ou "=" X
  m = s.match(/\b(?:alterar|editar|mudar)\s+(#\d+|id\s+[a-f0-9]{24}|[a-f0-9]{24}|[a-f0-9]{6})\s+(?:valor\s+|para\s+|=\s*)?([-\d.,]+)/i);
  if (m) {
    const ref = m[1].replace(/^id\s+/i, '').trim();
    return { cmd: 'changeAmount', ref, amount: m[2] };
  }

  // APAGAR
  m = s.match(/\b(?:apagar|excluir|deletar|remover)\s+(#\d+|id\s+[a-f0-9]{24}|[a-f0-9]{24}|[a-f0-9]{6})\b/i);
  if (m) {
    const ref = m[1].replace(/^id\s+/i, '').trim();
    return { cmd: 'deleteOne', ref };
  }

  return null;
}

// ===== EDIÇÃO ROBUSTA (busca primeiro, depois altera/apaga) =====
async function handleChangeCategory(msg, ref, newCatRaw) {
  const id = resolveRefToId(msg.from, ref);
  if (!id) { await msg.reply('Não consegui identificar o gasto (#n expirou?). Liste novamente e use #n, short id (6) ou id completo.'); return; }
  const newCat = ensureCategory(newCatRaw);

  let doc = await Expenses.findOne({ _id: new ObjectId(id), chatId: msg.from }) ||
            await Expenses.findOne({ _id: new ObjectId(id) });
  if (!doc) { await msg.reply('Gasto não encontrado. Liste novamente e tente com o id completo.'); return; }

  await Expenses.updateOne({ _id: doc._id }, { $set: { category: newCat, chatId: msg.from } });
  await msg.reply(`✅ Categoria atualizada para **${newCat}** em ${brl(doc.amount)} (id:${last6(doc._id)}).`);
}

async function handleChangeAmount(msg, ref, amountRaw) {
  const id = resolveRefToId(msg.from, ref);
  if (!id) { await msg.reply('Não consegui identificar o gasto (#n expirou?). Liste novamente e use #n, short id (6) ou id completo.'); return; }
  const amount = normalizeAmount(amountRaw);
  if (!amount) { await msg.reply('Valor inválido. Ex.: _alterar #2 para 120,50_'); return; }

  let doc = await Expenses.findOne({ _id: new ObjectId(id), chatId: msg.from }) ||
            await Expenses.findOne({ _id: new ObjectId(id) });
  if (!doc) { await msg.reply('Gasto não encontrado. Liste novamente e tente com o id completo.'); return; }

  await Expenses.updateOne({ _id: doc._id }, { $set: { amount, chatId: msg.from } });
  await msg.reply(`✅ Valor atualizado para **${brl(amount)}** na categoria **${doc.category}** (id:${last6(doc._id)}).`);
}

async function handleDeleteOne(msg, ref) {
  const id = resolveRefToId(msg.from, ref);
  if (!id) {
    await msg.reply('Não consegui identificar o gasto (#n expirou?). Liste novamente e use #n, short id (6) ou id completo.');
    return;
  }

  let doc = await Expenses.findOne({ _id: new ObjectId(id), chatId: msg.from }) ||
            await Expenses.findOne({ _id: new ObjectId(id) });

  if (!doc) {
    await msg.reply('Gasto não encontrado para este grupo. Liste novamente e tente com o id completo.');
    return;
  }

  const del = await Expenses.deleteOne({ _id: doc._id });
  if (del?.deletedCount === 1) {
    await msg.reply(`🗑️ Gasto apagado: **${brl(doc.amount)}** em **${doc.category}** (id:${last6(doc._id)}).`);
  } else {
    await msg.reply('Não consegui apagar. Tente novamente com o id completo.');
  }
}

// ========================= MAIN =========================
(async function main() {
  try {
    await mongo.connect();
    db = mongo.db(process.env.MONGODB_DB || 'wpp_expenses');
    Expenses = db.collection('expenses');

    await Expenses.createIndex({ chatId: 1, timestamp: -1 });
    await Expenses.createIndex({ category: 1 });
    await Expenses.createIndex({ payer: 1 });

    wpp.initialize();
  } catch (err) {
    console.error('Erro ao iniciar:', err);
    process.exit(1);
  }
})();

wpp.on('qr', (qr) => {
  console.log('Escaneie o QR para logar:');
  qrcode.generate(qr, { small: true });
});
wpp.on('ready', () => console.log('✅ WhatsApp pronto. Aguardando mensagens do grupo...'));

// ========================= HANDLER =========================
wpp.on('message', async (msg) => {
  try {
    if (msg.fromMe) return;
    if (!msg.from.endsWith('@g.us')) return;
    if (!ALLOW_ALL_GROUPS && GROUP_ID && msg.from !== GROUP_ID) return;

    const text = msg.body || '';
    const authorId = msg.author || msg._data?.author;
    const payer = payerFromAuthorId(authorId);

    // ===== 0) Comandos de LISTA/EDIÇÃO =====
    const admin = parseAdminCommand(text);
    if (admin) {
      if (admin.cmd === 'listByCat') return void (await handleListByCategory(msg, admin.cat, null, text));
      if (admin.cmd === 'changeCategory') return void (await handleChangeCategory(msg, admin.ref, admin.newCat));
      if (admin.cmd === 'changeAmount') return void (await handleChangeAmount(msg, admin.ref, admin.amount));
      if (admin.cmd === 'deleteOne') return void (await handleDeleteOne(msg, admin.ref));
    }

    // ===== 1) Requisição explícita para LISTAR por categoria =====
    if (isListRequest(text)) {
      const catCandidate = findCategoryInText(text);
      if (!catCandidate) {
        await msg.reply('Diga a categoria, por exemplo: "listar gastos de energeticos" ou "listar gastos de ifood".');
        return;
      }
      const cat = ensureCategory(catCandidate);
      const explicitPayer = getExplicitPayerFilter(text, payer); // só filtra se explicitamente dito
      return void (await handleListByCategory(msg, cat, explicitPayer, text));
    }

    // ===== 2) Múltiplos lançamentos na mesma msg =====
    const multi = parseMultipleRecords(text);
    if (multi.length >= 2) {
      const docs = multi.map(it => ({
        chatId: msg.from,
        messageId: msg.id?._serialized || null,
        timestamp: new Date(),
        originalText: text,
        amount: it.amount,
        currency: 'BRL',
        category: ensureCategory(it.category),
        payer,
      }));
      if (docs.length) {
        await Expenses.insertMany(docs);
        const resumo = docs.map(d => `${d.category} ${brl(d.amount)}`).join(', ');
        await msg.reply(`✅ ${docs.length} gastos adicionados: ${resumo} (${payer || 'indefinido'}).`);
        return;
      }
    }

    // ===== 3) Classificação IA: record vs query =====
    const analysis = await analyzeWithGPT(text, { payer });

    // ===== RECORD =====
    if (analysis.action === 'record') {
      const single = parseSingleRecord(text);
      if (single) {
        const doc = {
          chatId: msg.from,
          messageId: msg.id?._serialized || null,
          timestamp: new Date(),
          originalText: text,
          amount: single.amount,
          currency: 'BRL',
          category: ensureCategory(single.category),
          payer,
        };
        await Expenses.insertOne(doc);
        await msg.reply(`✅ Gasto **${doc.category}** de **${brl(doc.amount)}** (${payer || 'indefinido'}) adicionado com sucesso.`);
        return;
      }

      const amount = normalizeAmount(analysis.amount);
      const category = ensureCategory(analysis.category || 'Diversos');
      if (!amount) {
        await msg.reply('Não entendi o lançamento. Exemplos: "paiol 16", "monster 11", "uber 29,90".');
        return;
      }
      await Expenses.insertOne({
        chatId: msg.from,
        messageId: msg.id?._serialized || null,
        timestamp: new Date(),
        originalText: text,
        amount,
        currency: 'BRL',
        category,
        payer,
      });
      await msg.reply(`✅ Gasto **${category}** de **${brl(amount)}** (${payer || 'indefinido'}) adicionado com sucesso.`);
      return;
    }

    // ===== QUERY (SOMA) =====
    if (analysis.action === 'query') {
      const q = { chatId: msg.from };

      // Categoria: do modelo se vier, senão tenta achar no texto
      const catFromModel = analysis?.filters?.category ? ensureCategory(analysis.filters.category) : null;
      const catFromText = findCategoryInText(text);
      const cat = ensureCategory(catFromModel || catFromText || '');
      if (cat && cat !== '') q.category = { $regex: new RegExp(`^${escapeRegex(cat)}$`, 'i') };

      // Payer: só filtra se explicitamente dito no texto
      const explicitPayer = getExplicitPayerFilter(text, payer);
      if (explicitPayer) q.payer = explicitPayer;

      // Período: SEMPRE mês atual por padrão; se texto indica outro, respeita
      const p = getPeriodFromText(text);
      let start = p?.start, end = p?.end, label = p?.label;
      if (!start || !end) { start = toJSDate(startOfMonth()); end = toJSDate(endOfMonth()); label = 'este mês'; }
      q.timestamp = { $gte: start, $lt: end };

      const agg = await Expenses.aggregate([
        { $match: q },
        { $group: { _id: null, total: { $sum: '$amount' }, count: { $sum: 1 } } },
      ]).toArray();

      const total = agg?.[0]?.total || 0;
      const count = agg?.[0]?.count || 0;

      const catStr = q.category ? ` em "${cat}"` : '';
      const payerStr = q.payer ? ` (${q.payer})` : '';

      if (count === 0) {
        await msg.reply(`Não encontrei gastos${catStr}${payerStr} (${label}).`);
      } else {
        await msg.reply(`Você gastou **${brl(total)}**${catStr}${payerStr} em **${count}** lançamento(s) (${label}).`);
      }
      return;
    }

    // ===== HELP =====
    if (/^help$|^ajuda$/i.test(text)) {
      await msg.reply(
        'Regras de período: por padrão SEMPRE mostro o mês atual.\n' +
        'Para outro período, especifique no texto: "mês passado"/"mês anterior" ou "anual/este ano".\n\n' +
        'Exemplos:\n' +
        '- Lançar múltiplos:  paiol 16 e monster 11\n' +
        '- Listar (mês atual): me liste individualmente todos os gastos de energeticos\n' +
        '- Listar (mês passado): listar gastos de energeticos do mês passado\n' +
        '- Listar (anual):      listar gastos de energeticos anual\n' +
        '- Somar (mês atual):   quanto gastei com energeticos\n' +
        '- Somar (mês passado): quanto gastei com energeticos mês anterior\n' +
        '- Editar:              mover #2 para transportes | alterar #2 para 12,90 | apagar #1\n' +
        '- Também aceita short id (6): apagar c67f04'
      );
      return;
    }

    await msg.reply('Período padrão: mês atual. Para mês anterior ou anual, cite isso na mensagem. Ex.: "listar energeticos mês passado".');
  } catch (err) {
    console.error('Erro no handler:', err);
    try { await msg.reply('Ocorreu um erro ao processar.'); } catch {}
  }
});

wpp.on('disconnected', (r) => console.log('Disconnected:', r));
process.on('SIGINT', async () => { console.log('\nEncerrando...'); try { await mongo.close(); } catch {} process.exit(0); });
