// «Моя коллекция»: библиотека из Framesearch (https://github.com/PsyGioX/framesearch).
// Framesearch хранит всё в IndexedDB своего сайта, поэтому сюда коллекция попадает через
// его экспорт (.framesearch / .json, можно зашифрованный) или через код «Поделиться» (P:… / E:…).
// Коллекция хранится только в этом браузере. В комнату уходит лишь выбранное видео.

const DB_NAME = "seans-library", STORE = "kv";

function idb() {
  return new Promise((res, rej) => {
    let r;
    try { r = indexedDB.open(DB_NAME, 1); } catch (e) { rej(e); return; }
    r.onupgradeneeded = () => r.result.createObjectStore(STORE);
    r.onsuccess = () => res(r.result);
    r.onerror = () => rej(r.error);
  });
}
async function kvGet(key) {
  try { const db = await idb(); return await new Promise(res => { const q = db.transaction(STORE).objectStore(STORE).get(key); q.onsuccess = () => res(q.result ?? null); q.onerror = () => res(null); }); }
  catch { return null; }
}
async function kvSet(key, val) {
  try { const db = await idb(); await new Promise(res => { const t = db.transaction(STORE, "readwrite"); t.objectStore(STORE).put(val, key); t.oncomplete = res; t.onerror = res; }); } catch {}
}
async function kvDel(key) {
  try { const db = await idb(); await new Promise(res => { const t = db.transaction(STORE, "readwrite"); t.objectStore(STORE).delete(key); t.oncomplete = res; t.onerror = res; }); } catch {}
}

// --- Framesearch formats -------------------------------------------------------------
const b64ToBytes = s => Uint8Array.from(atob(s), c => c.charCodeAt(0));
const b64ToUnicode = s => new TextDecoder().decode(b64ToBytes(s));
const looksEncrypted = s => /^[A-Za-z0-9+/\r\n\s]+={0,2}\s*$/.test(s) && !/^\s*[{[]/.test(s);

// Same scheme as Framesearch: base64(salt[16] + iv[12] + AES-GCM ciphertext), PBKDF2-SHA256 100000
async function decrypt(text, password) {
  const data = b64ToBytes(String(text).replace(/[\r\n\s]/g, ""));
  if (data.length < 29) throw new Error("Файл повреждён или это не экспорт Framesearch.");
  const enc = new TextEncoder();
  const base = await crypto.subtle.importKey("raw", enc.encode(password), { name: "PBKDF2" }, false, ["deriveKey"]);
  const key = await crypto.subtle.deriveKey({ name: "PBKDF2", salt: data.slice(0, 16), iterations: 100000, hash: "SHA-256" }, base, { name: "AES-GCM", length: 256 }, false, ["decrypt"]);
  try {
    const plain = await crypto.subtle.decrypt({ name: "AES-GCM", iv: data.slice(16, 28) }, key, data.slice(28));
    return new TextDecoder().decode(plain);
  } catch { throw new Error("Неверный пароль."); }
}

const str = (v, n) => (typeof v === "string" ? v : v == null ? "" : String(v)).slice(0, n);
function cleanVideo(v) {
  return {
    id: v.id, title: str(v.title, 200) || "Без названия", year: str(v.year, 10), type: str(v.type, 20),
    genre: str(v.genre, 80), poster: str(v.poster, 3_000_000), sourceType: str(v.sourceType, 30),
    sourceUrl: str(v.sourceUrl, 50_000_000), sourceCategory: str(v.sourceCategory, 30)
  };
}
function cleanEpisode(e) {
  return { videoId: e.videoId, season: Number(e.season) || 1, episode: Number(e.episode) || 0, title: str(e.title, 200), sourceType: str(e.sourceType, 30), sourceUrl: str(e.sourceUrl, 50_000_000) };
}
function normalize(obj) {
  if (!obj || typeof obj !== "object") throw new Error("Это не экспорт Framesearch.");
  if (obj.video) obj = { videos: [obj.video], episodes: obj.episodes || [] }; // share code
  if (!Array.isArray(obj.videos)) throw new Error("Это не экспорт Framesearch: в файле нет списка видео.");
  const videos = obj.videos.filter(v => v && typeof v === "object").map(cleanVideo);
  const episodes = (Array.isArray(obj.episodes) ? obj.episodes : []).filter(e => e && typeof e === "object").map(cleanEpisode);
  return { videos, episodes };
}

export async function parseExport(text, password) {
  text = String(text || "").trim();
  if (/^\s*[{[]/.test(text)) return normalize(JSON.parse(text));
  if (!looksEncrypted(text)) throw new Error("Это не экспорт Framesearch.");
  if (!password) { const e = new Error("Файл зашифрован. Введите пароль, который задавали при экспорте."); e.needPassword = true; throw e; }
  return normalize(JSON.parse(await decrypt(text, password)));
}

export const isShareCode = s => /^(P|E):[A-Za-z0-9+/=\s]{8,}$/.test(String(s || "").trim());
export async function parseShareCode(code, password) {
  code = String(code).trim();
  if (code.startsWith("P:")) return normalize(JSON.parse(b64ToUnicode(code.slice(2).replace(/\s/g, ""))));
  if (!password) { const e = new Error("Код зашифрован. Введите пароль."); e.needPassword = true; throw e; }
  return normalize(JSON.parse(await decrypt(code.slice(2), password)));
}

// --- storage ---------------------------------------------------------------------------
let lib = null;
export async function loadLibrary() { if (lib) return lib; lib = await kvGet("library"); return lib; }
export async function saveLibrary(data) { lib = { ...data, savedAt: Date.now() }; await kvSet("library", lib); return lib; }
export async function clearLibrary() { lib = null; await kvDel("library"); }

// --- mapping a Framesearch entry to something the room can play in sync ------------------
// parseSource comes from app.js (YouTube, RuTube, direct links).
export function toRoomSource(item, title, parseSource) {
  const url = item.sourceUrl || "";
  const cat = item.sourceCategory || "";
  if (!url) return { error: "У этого видео в коллекции нет ссылки." };
  if (/^data:video\//i.test(url) || /^blob:/i.test(url) || item.sourceType === "file") {
    return /^data:video\//i.test(url) ? { file: url } : { error: "Это локальный файл, который Framesearch не сохранил в экспорт. Откройте его кнопкой «Свой файл»." };
  }
  if (cat === "balancer") return { error: "Видео из балансеров нельзя ставить в «Общий сеанс». Подходят YouTube, RuTube и прямые ссылки на видеофайлы." };
  const src = parseSource(url);
  if (!src || src.search || src.error) return { error: "Эту ссылку нельзя синхронизировать." };
  if (src.type === "url" && (cat === "custom" || item.sourceType === "iframe" || cat === "social")) {
    return { error: "Это страница со своим плеером, а не видеофайл. Синхронно можно смотреть YouTube, RuTube и прямые ссылки на .mp4, .webm, .m3u8." };
  }
  return { src: { ...src, title: String(title).slice(0, 160) } };
}

export function dataUrlToFile(dataUrl, name) {
  const [head, body] = dataUrl.split(",", 2);
  const mime = (head.match(/^data:([^;]+)/) || [, "video/mp4"])[1];
  const bin = head.includes(";base64") ? b64ToBytes(body) : new TextEncoder().encode(decodeURIComponent(body));
  const ext = (mime.split("/")[1] || "mp4").replace(/[^a-z0-9]/gi, "");
  return new File([bin], `${name.replace(/[\\/:*?"<>|]/g, " ").slice(0, 120)}.${ext}`, { type: mime });
}
