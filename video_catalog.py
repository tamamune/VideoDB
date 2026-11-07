# -*- coding: utf-8 -*-
"""
動画カタログ (Windows / Python 3 / tkinter)

NAS上の動画フォルダを読み込んで一覧化し、サムネイル・ジャンル・グループ管理、
同一動画(ハッシュ)/類似動画(名前)検出、検索ができるアプリ。
データ(JSON + サムネイル)は Google ドライブの同期フォルダに保存する。
"""
import os
import re
import sys
import json
import queue
import hashlib
import difflib
import threading
import unicodedata
import subprocess
import shutil
import time
from collections import defaultdict

import tkinter as tk
from tkinter import ttk, messagebox, filedialog

import cv2
from PIL import Image, ImageTk

APP = "VideoCatalog"
VIDEO_EXT = {".mp4", ".mkv", ".avi", ".mov", ".wmv", ".flv", ".m4v", ".ts", ".m2ts",
             ".mpg", ".mpeg", ".webm", ".rmvb", ".divx", ".3gp", ".ogm", ".vob"}
DEFAULT_GENRES = ["ドラマ", "映画", "アニメ", "バラエティ", "ドキュメンタリー", "音楽", "スポーツ", "その他"]
SETTINGS_PATH = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), APP, "settings.json")
THUMB_W, THUMB_H = 640, 360
CHUNK = 1024 * 1024


# ----------------------------------------------------------------- 設定 / 保存
def default_data_dir():
    cands = []
    for l in "GHIJKLMNOP":
        cands += [f"{l}:\\マイドライブ", f"{l}:\\My Drive"]
    home = os.path.expanduser("~")
    cands += [os.path.join(home, "Google Drive"), os.path.join(home, "マイドライブ"),
              os.path.join(home, "My Drive")]
    for c in cands:
        if os.path.isdir(c):
            return os.path.join(c, APP)
    return os.path.join(home, "Documents", APP)


def load_settings():
    s = {"data_dir": "", "thumb_mode": 1, "hash_mode": "quick", "sim_threshold": 0.8,
         "path_map": [], "sheet_url": "", "sa_json": "", "sheet_auto": False, "col_widths": {}, "side_w": 300, "side_show": True}
    try:
        with open(SETTINGS_PATH, encoding="utf-8") as f:
            s.update(json.load(f))
    except (OSError, ValueError):
        pass
    if not s["data_dir"]:
        s["data_dir"] = default_data_dir()
    return s


def save_settings(s):
    os.makedirs(os.path.dirname(SETTINGS_PATH), exist_ok=True)
    with open(SETTINGS_PATH, "w", encoding="utf-8") as f:
        json.dump(s, f, ensure_ascii=False, indent=2)


def atomic_write_json(path, obj):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, ensure_ascii=False, indent=1)
    os.replace(tmp, path)


class Store:
    """一覧(リスト)ごとに1つのJSONファイルで管理する。"""
    BAD = set('\\/:*?"<>|')

    def __init__(self, data_dir):
        self.root = data_dir
        self.lists_dir = os.path.join(data_dir, "lists")
        self.thumbs_dir = os.path.join(data_dir, "thumbs")
        os.makedirs(self.lists_dir, exist_ok=True)
        os.makedirs(self.thumbs_dir, exist_ok=True)
        self.bases = {}   # 読込/保存時点の各項目の状態 (変更検出用)
        self.mtimes = {}  # 読込/保存時点のファイル更新時刻

    def _p(self, name):
        return os.path.join(self.lists_dir, name + ".json")

    def names(self):
        return sorted(f[:-5] for f in os.listdir(self.lists_dir) if f.endswith(".json"))

    def valid_name(self, name):
        return bool(name.strip()) and not (set(name) & self.BAD)

    @staticmethod
    def _dump(it):
        return json.dumps({k: v for k, v in it.items() if k not in ("flags", "ut", "lpath", "sy")},
                          sort_keys=True, ensure_ascii=False)

    def _remember(self, name, data):
        self.bases[name] = {it["id"]: self._dump(it) for it in data["items"]}
        self.mtimes[name] = self.mtime(name)

    def mtime(self, name):
        try:
            return os.path.getmtime(self._p(name))
        except OSError:
            return None

    def changed_externally(self, name):
        return self.mtime(name) != self.mtimes.get(name)

    def load(self, name):
        with open(self._p(name), encoding="utf-8") as f:
            d = json.load(f)
        d.setdefault("items", [])
        d.setdefault("deleted", {})
        self._remember(name, d)
        return d

    @staticmethod
    def _merge(data, disk):
        """他の端末が先に保存していた場合、項目単位で新しい方を採用してマージする。"""
        mine_del = dict(data["deleted"])
        theirs_del = disk.get("deleted", {})
        ours = {i["id"]: i for i in data["items"]}
        theirs = {i["id"]: i for i in disk.get("items", [])}
        out = []
        for iid in list(ours) + [i for i in theirs if i not in ours]:
            o, t = ours.get(iid), theirs.get(iid)
            if o and t:
                out.append(t if t.get("ut", 0) > o.get("ut", 0) else o)
            elif o:
                if theirs_del.get(iid, 0) <= o.get("ut", 0):
                    out.append(o)
            elif mine_del.get(iid, 0) <= t.get("ut", 0):
                out.append(t)
        data["items"] = out
        merged = dict(theirs_del)
        for k, v in mine_del.items():
            merged[k] = max(v, merged.get(k, 0))
        ids = {i["id"] for i in out}
        data["deleted"] = {k: v for k, v in merged.items() if k not in ids}

    def save(self, name, data, merge=True):
        now = time.time()
        base = self.bases.get(name, {})
        dele = data.setdefault("deleted", {})
        ids = set()
        for it in data["items"]:
            ids.add(it["id"])
            if base.get(it["id"]) != self._dump(it):
                it["ut"] = now
            else:
                it.setdefault("ut", 0)
        for i in base:
            if i not in ids:
                dele[i] = now
        for i in ids:
            dele.pop(i, None)
        if merge and os.path.exists(self._p(name)) and self.changed_externally(name):
            try:
                with open(self._p(name), encoding="utf-8") as f:
                    self._merge(data, json.load(f))
            except (OSError, ValueError):
                pass
        atomic_write_json(self._p(name), data)
        self._remember(name, data)

    def create(self, name):
        self.save(name, {"name": name, "items": [], "deleted": {}}, merge=False)

    def delete(self, name):
        os.remove(self._p(name))

    def rename(self, old, new):
        d = self.load(old)
        d["name"] = new
        self.save(new, d, merge=False)
        os.remove(self._p(old))


# ----------------------------------------------------------------- 解析ロジック
def natural_key(s):
    return [int(t) if t.isdigit() else t.lower() for t in re.split(r"(\d+)", s)]


def fmt_size(n):
    for u in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or u == "TB":
            return f"{n:.0f}{u}" if u == "B" else f"{n:.1f}{u}"
        n /= 1024


def fmt_dur(sec):
    sec = int(sec or 0)
    if sec <= 0:
        return ""
    return f"{sec // 3600}:{sec % 3600 // 60:02d}:{sec % 60:02d}"


def quick_hash(path, size):
    """先頭・中央・末尾 各1MB + サイズ のSHA1。NASでも高速。"""
    h = hashlib.sha1()
    h.update(str(size).encode())
    with open(path, "rb") as f:
        for pos in (0, max(0, size // 2 - CHUNK // 2), max(0, size - CHUNK)):
            f.seek(pos)
            h.update(f.read(CHUNK))
    return h.hexdigest()


def full_hash(path):
    h = hashlib.sha1()
    with open(path, "rb") as f:
        while True:
            b = f.read(8 * CHUNK)
            if not b:
                break
            h.update(b)
    return h.hexdigest()


_NOISE = re.compile(
    r"\[[^\]]*\]|【[^】]*】|\([^)]*\)|（[^）]*）"
    r"|\b(?:2160p|1080[pi]|720p|480p|4k|x26[45]|h\.?26[45]|hevc|avc|aac|flac|ac3|"
    r"bd|bdrip|bluray|web-?dl|webrip|dvdrip|hdtv|hdr|10bit)\b")
_EPISODE = re.compile(
    r"第\s*\d+\s*[話回章巻夜]|#\s*\d+|\bs\d+\s*e\d+\b|\bep?\.?\s*\d+\b|\bvol\.?\s*\d+\b|\bpart\s*\d+\b",
    re.I)


def normalize_title(title):
    t = unicodedata.normalize("NFKC", title).lower()
    t = _NOISE.sub(" ", t)
    t = _EPISODE.sub(" ", t)
    return re.sub(r"[\W_]+", "", t)


def make_thumb(path, mode, out):
    """1コマ or 4コマのサムネイルを作成し、動画の長さ(秒)を返す。失敗時 None。"""
    cap = cv2.VideoCapture(path)
    try:
        if not cap.isOpened():
            return None
        n = cap.get(cv2.CAP_PROP_FRAME_COUNT) or 0
        fps = cap.get(cv2.CAP_PROP_FPS) or 0
        dur = n / fps if fps > 0 and n > 0 else 0
        points = [0.1] if mode == 1 else [0.1, 0.35, 0.6, 0.85]
        tw, th = (THUMB_W, THUMB_H) if mode == 1 else (THUMB_W // 2, THUMB_H // 2)
        canvas = Image.new("RGB", (THUMB_W, THUMB_H), (0, 0, 0))
        got = 0
        for i, p in enumerate(points):
            if n > 0:
                cap.set(cv2.CAP_PROP_POS_FRAMES, int(n * p))
            ok, fr = cap.read()
            if not ok:
                continue
            got += 1
            im = Image.fromarray(cv2.cvtColor(fr, cv2.COLOR_BGR2RGB))
            im.thumbnail((tw, th))
            x = (i % 2) * tw if mode != 1 else 0
            y = (i // 2) * th if mode != 1 else 0
            canvas.paste(im, (x + (tw - im.width) // 2, y + (th - im.height) // 2))
        if not got:
            return None
        canvas.save(out, "JPEG", quality=80)
        return dur
    finally:
        cap.release()


def scan_videos(root, group_root_files):
    """root配下の動画を列挙。2本以上の動画があるフォルダはフォルダ名でグループ化する。"""
    root = os.path.normpath(root)
    base = os.path.basename(root) or root
    result = []
    for dirpath, _dirs, files in os.walk(root):
        vids = [f for f in files if os.path.splitext(f)[1].lower() in VIDEO_EXT]
        if not vids:
            continue
        rel = os.path.relpath(dirpath, root)
        if rel == ".":
            group = base if (len(vids) >= 2 and group_root_files) else ""
        else:
            group = " / ".join([base] + rel.split(os.sep)) if len(vids) >= 2 else ""
            if len(vids) < 2:
                group = ""
        for f in vids:
            result.append((os.path.join(dirpath, f), group))
    return result


def _map(p, pairs):
    p = p.replace("/", "\\")
    pl = p.lower()
    for a, b in pairs:
        al = a.replace("/", "\\").lower().rstrip("\\")
        if al and (pl == al or pl.startswith(al + "\\")):
            return b.rstrip("\\") + p[len(al):]
    return p


def to_local(p, pmap):
    """共通パス(データ内) → この端末のパス"""
    return _map(p, pmap)


def to_canon(p, pmap):
    """この端末のパス → 共通パス(データ内)"""
    return _map(p, [(b, a) for a, b in pmap])


def parse_pmap(text):
    out = []
    for line in text.splitlines():
        if "=" in line:
            a, b = line.split("=", 1)
            if a.strip() and b.strip():
                out.append([a.strip(), b.strip()])
    return out


HOWTO = r"""【他の端末でこのアプリを使う手順】
1. Python 3 をインストール (https://www.python.org/ ・「Add python.exe to PATH」にチェック)
2. このフォルダの中身をPCの任意の場所へコピーし、コマンドプロンプトで
     pip install -r requirements.txt
3. start.bat をダブルクリックで起動
4. 右上の「設定」で
   ・データ保存先: Googleドライブ(同期フォルダ)の VideoCatalog フォルダ(このフォルダの1つ上)を指定
     (通常は自動で見つかります)
   ・パス対応: NASのパスが端末ごとに違う場合のみ。1行に「データ内のパス=この端末でのパス」
       例)  Z:\video=\\NAS\share\video
5. 一覧やジャンルの変更はGoogleドライブ経由で自動共有され、約5秒ごとに他の端末の変更が反映されます。
   同時に別の端末で編集しても項目単位でマージされます(同じ項目なら新しい方が優先)。
"""


def publish_app(data_dir):
    """アプリ本体と使い方をGoogleドライブのデータフォルダに置き、他の端末から取り出せるようにする。"""
    try:
        dst = os.path.join(data_dir, "app")
        src_dir = os.path.dirname(os.path.abspath(__file__))
        if os.path.normcase(os.path.abspath(dst)) == os.path.normcase(src_dir):
            return
        os.makedirs(dst, exist_ok=True)
        for f in ("video_catalog.py", "start.bat", "requirements.txt"):
            sp = os.path.join(src_dir, f)
            if os.path.exists(sp):
                shutil.copy2(sp, os.path.join(dst, f))
        with open(os.path.join(dst, "他の端末での使い方.txt"), "w", encoding="utf-8") as fh:
            fh.write(HOWTO)
    except OSError:
        pass


def item_id(path):
    return hashlib.sha1(os.path.normcase(path).encode("utf-8")).hexdigest()[:12]


# ----------------------------------------------------------------- バックグラウンドジョブ
def job_thumbs(items, mode, thumbs_dir, force, q):
    total = len(items)
    for i, it in enumerate(items, 1):
        q.put(("progress", i, total, f"サムネイル作成 ({i}/{total}) {it['title']}"))
        out = os.path.join(thumbs_dir, f"{it['id']}_{mode}.jpg")
        try:
            if os.path.exists(out) and not force:
                q.put(("thumb", it["id"], None, os.path.basename(out), mode))
                continue
            dur = make_thumb(it.get("lpath") or it["path"], mode, out)
        except Exception:
            dur = None
        if dur is not None:
            q.put(("thumb", it["id"], dur, os.path.basename(out), mode))


def job_analyze(items, hash_mode, thr, q):
    full = hash_mode == "full"
    hkey = "hf" if full else "hq"
    flags = {it["id"]: [] for it in items}
    newhash = {}
    same_pairs = set()

    def add(a, b, kind, score):
        flags[a["id"]].append({"id": b["id"], "kind": kind, "score": round(score, 3),
                               "name": b["title"], "path": b["path"]})

    # 1) 同一判定: サイズが一致するものだけハッシュ計算(NAS負荷を最小化)
    by_size = defaultdict(list)
    for it in items:
        if it["size"] > 0:
            by_size[it["size"]].append(it)
    cands = [(s, l) for s, l in by_size.items() if len(l) > 1]
    total = sum(len(l) for _, l in cands)
    n = 0
    for size, lst in cands:
        byh = defaultdict(list)
        for it in lst:
            n += 1
            q.put(("progress", n, total, f"ハッシュ計算 ({n}/{total}) {it['title']}"))
            h = it.get(hkey)
            if not h:
                try:
                    lp = it.get("lpath") or it["path"]
                    h = full_hash(lp) if full else quick_hash(lp, size)
                except OSError:
                    continue
                newhash[it["id"]] = (hkey, h)
            byh[h].append(it)
        for grp in byh.values():
            if len(grp) > 1:
                for a in grp:
                    for b in grp:
                        if a is not b:
                            add(a, b, "same", 1.0)
                            same_pairs.add(frozenset((a["id"], b["id"])))

    # 2) 類似判定: 正規化したタイトルの文字列類似度
    keyed = [(it, normalize_title(it["title"])) for it in items]
    keyed = [(it, k) for it, k in keyed if len(k) >= 3]
    total = len(keyed)
    sm = difflib.SequenceMatcher(None, autojunk=False)
    for i, (a, ka) in enumerate(keyed):
        if i % 20 == 0:
            q.put(("progress", i, total, f"名前の類似チェック ({i}/{total})"))
        sm.set_seq2(ka)
        for b, kb in keyed[i + 1:]:
            if a["group"] and a["group"] == b["group"]:
                continue  # 同じグループ内(話数違い)は対象外
            if frozenset((a["id"], b["id"])) in same_pairs:
                continue
            sm.set_seq1(kb)
            if sm.real_quick_ratio() < thr or sm.quick_ratio() < thr:
                continue
            r = sm.ratio()
            if r >= thr:
                add(a, b, "similar", r)
                add(b, a, "similar", r)
    for l in flags.values():
        l.sort(key=lambda f: (f["kind"] != "same", -f["score"]))
    q.put(("flags", flags, newhash))


def job_scan(root, group_root_files, existing_items, mode, hash_mode, thr, thumbs_dir, pmap, q):
    q.put(("status", "フォルダを検索中…(NASの場合は時間がかかります)"))
    known = {os.path.normcase(it["path"]) for it in existing_items}
    pmap = [tuple(x) for x in pmap]
    new = []
    found = scan_videos(root, group_root_files)
    for i, (path, group) in enumerate(found, 1):
        canon = to_canon(path, pmap)
        if os.path.normcase(canon) in known:
            continue
        try:
            st = os.stat(path)
        except OSError:
            continue
        title = os.path.splitext(os.path.basename(path))[0]
        new.append({"id": item_id(canon), "path": canon, "lpath": path, "title": title, "size": st.st_size,
                    "mtime": int(st.st_mtime), "duration": 0, "group": group, "genre": "",
                    "hq": "", "hf": "", "thumb": "", "thumb_mode": 0, "flags": []})
        if i % 50 == 0:
            q.put(("status", f"検索中… {i}/{len(found)}"))
    q.put(("items", new, len(found)))
    job_thumbs(new, mode, thumbs_dir, False, q)
    job_analyze([dict(it) for it in existing_items] + new, hash_mode, thr, q)


# ----------------------------------------------------------------- ファイル移動
def job_move(moves, dest_dir, set_group, pmap, q):
    """moves: [(id, この端末でのパス)] を dest_dir へ実際に移動する。"""
    pmap = [tuple(x) for x in pmap]
    total = len(moves)
    group = os.path.basename(os.path.normpath(dest_dir)) if set_group else None
    for i, (iid, src) in enumerate(moves, 1):
        q.put(("progress", i, total, f"移動中 ({i}/{total}) {os.path.basename(src)}"))
        dst = os.path.join(dest_dir, os.path.basename(src))
        try:
            if not os.path.exists(src):
                raise FileNotFoundError("移動元が見つかりません")
            if os.path.normcase(os.path.abspath(src)) == os.path.normcase(os.path.abspath(dst)):
                raise ValueError("移動先が同じフォルダです")
            if os.path.exists(dst):
                raise FileExistsError("移動先に同名のファイルがあります")
            shutil.move(src, dst)
            q.put(("moved", iid, to_canon(dst, pmap), group))
        except Exception as e:  # noqa
            q.put(("move_err", f"{os.path.basename(src)}: {e}"))


# ----------------------------------------------------------------- スプレッドシート連携 (Google Sheets API)
SHEET_COLS = ["id", "タイトル", "グループ", "ジャンル", "時間(秒)", "サイズ(byte)", "パス", "更新"]


def sheet_open(s):
    try:
        import gspread
    except ImportError:
        raise RuntimeError("gspread が未インストールです。  pip install gspread  を実行してください。")
    if not s.get("sheet_url") or not s.get("sa_json"):
        raise RuntimeError("設定でスプレッドシートのURLとサービスアカウントJSONを指定してください。")
    try:
        with open(s["sa_json"], encoding="utf-8") as f:
            kind = json.load(f)
    except (OSError, ValueError) as e:
        raise RuntimeError(f"認証JSONを読めません: {s['sa_json']}\n{e}")
    if kind.get("type") == "service_account":
        gc = gspread.service_account(filename=s["sa_json"])
    else:  # OAuthクライアント(client_secret.json): 初回のみブラウザで許可。トークンはアプリ専用ファイルに保存
        tok = os.path.join(os.path.dirname(SETTINGS_PATH), "sheets_token.json")
        gc = gspread.oauth(credentials_filename=s["sa_json"], authorized_user_filename=tok)
    u = s["sheet_url"].strip()
    return gc.open_by_url(u) if u.startswith("http") else gc.open_by_key(u)


def _sy(title, group, genre, path):
    return json.dumps([title, group, genre, path], ensure_ascii=False)


def _int(v):
    try:
        return int(float(str(v).replace(",", "").strip()))
    except ValueError:
        return 0


def _is_app_tab(vals):
    return bool(vals) and vals[0][:1] == ["id"]


def _blank(vals):
    return not any(c.strip() for r in vals for c in r)


def sync_one(sh, ws, vals, list_name, items, deleted):
    """1つの一覧とシート(タブ)を双方向同期する。ws が None なら新規作成。
    戻り値: (updates, new, syncs)。シート側で編集された項目(タイトル/グループ/ジャンル/パス)は取り込み、
    アプリ側の変更とシート未登録の項目はシートへ書き出す。"""
    if ws is None:
        ws = sh.add_worksheet(title=list_name, rows=max(100, len(items) + 50), cols=len(SHEET_COLS))
        vals = []
    remote, norows = {}, []
    if not _blank(vals):
        if not _is_app_tab(vals):
            raise RuntimeError(f"シート「{list_name}」は本アプリの形式ではありません(1行目の先頭が id ではない)。\n"
                               "既存データを壊さないため同期を中止しました。別の名前の一覧で同期してください。")
        idx = {h.strip(): i for i, h in enumerate(vals[0])}

        def g(r, name):
            i = idx.get(name)
            return r[i].strip() if i is not None and i < len(r) else ""
        for r in vals[1:]:
            if not any(c.strip() for c in r):
                continue
            rec = {"title": g(r, "タイトル"), "group": g(r, "グループ"), "genre": g(r, "ジャンル"),
                   "path": g(r, "パス"), "duration": _int(g(r, "時間(秒)")), "size": _int(g(r, "サイズ(byte)"))}
            if not rec["title"]:
                continue
            if g(r, "id"):
                remote[g(r, "id")] = rec
            else:
                norows.append(rec)
    byid = {it["id"]: it for it in items}
    updates, new = {}, []
    for iid, rec in remote.items():
        it = byid.get(iid)
        if it:
            if it.get("sy") and _sy(rec["title"], rec["group"], rec["genre"], rec["path"]) != it["sy"]:
                updates[iid] = {k: rec[k] for k in ("title", "group", "genre", "path")}
        elif iid not in deleted:
            new.append(dict(rec, id=iid, mtime=0, hq="", hf="", thumb="", thumb_mode=0, flags=[]))
    for rec in norows:
        iid = item_id("sheet:" + list_name + ":" + rec["title"] + ":" + rec["path"])
        if iid not in byid and iid not in remote:
            new.append(dict(rec, id=iid, mtime=0, hq="", hf="", thumb="", thumb_mode=0, flags=[]))
    final = [dict(it, **updates.get(it["id"], {})) for it in items] + new
    rows = [SHEET_COLS]
    for it in final:
        rows.append([it["id"], it["title"], it["group"], it["genre"], int(it.get("duration") or 0),
                     it.get("size", 0), it["path"],
                     time.strftime("%Y-%m-%d %H:%M", time.localtime(it.get("ut") or time.time()))])
    ws.clear()
    ws.resize(rows=max(len(rows) + 20, 100), cols=len(SHEET_COLS))
    ws.update(range_name="A1", values=rows, value_input_option="RAW")
    syncs = {it["id"]: _sy(it["title"], it["group"], it["genre"], it["path"]) for it in final}
    return updates, new, syncs


def apply_sheet_result(items, upd, new, syncs):
    """sync_one の結果を items(リスト)へ反映する。"""
    for it in items:
        it.update(upd.get(it["id"], {}))
        if it["id"] in syncs:
            it["sy"] = syncs[it["id"]]
    have = {it["id"] for it in items}
    for n in new:
        if n["id"] not in have:
            n["sy"] = syncs.get(n["id"], "")
            items.append(n)


def pull_foreign(vals, list_name, items):
    """アプリ形式ではないシート(自分で作った表)を読み取り専用で取り込む。シートは書き換えない。"""
    if len(vals) < 2:
        return {}, []
    hdr = [h.strip().lower() for h in vals[0]]

    def col(names):
        for n in names:
            if n in hdr:
                return hdr.index(n)
        return None
    ti = col(["タイトル", "title", "名前", "作品名", "作品", "ファイル名", "題名", "name"])
    ti = 0 if ti is None else ti
    pi, gi, ji = col(["パス", "path"]), col(["グループ", "group"]), col(["ジャンル", "genre"])

    def cell(r, i):
        return r[i].strip() if i is not None and i < len(r) else ""
    byid = {it["id"]: it for it in items}
    updates, new, seen = {}, [], defaultdict(int)
    for r in vals[1:]:
        title = cell(r, ti)
        if not title:
            continue
        path = cell(r, pi)
        key = f"sheet:{list_name}:{title}:{path}"
        seen[key] += 1
        iid = item_id(key + (f"#{seen[key]}" if seen[key] > 1 else ""))
        rec = {"title": title, "group": cell(r, gi), "genre": cell(r, ji), "path": path}
        it = byid.get(iid)
        if it is None:
            new.append(dict(rec, id=iid, size=0, duration=0, mtime=0, hq="", hf="", thumb="", thumb_mode=0, flags=[]))
        elif any(it.get(k) != v for k, v in rec.items()):
            updates[iid] = rec
    return updates, new


def job_sheet_sync(s, cur_name, cur_items, cur_deleted, data_dir, cur_ro, q):
    """全ての一覧 ⇔ シート(タブ)を同期。一覧名 = シート名。
    シート側にだけある本アプリ形式のタブは一覧として追加する。"""
    q.put(("status", "スプレッドシートと同期中…"))
    sh = sheet_open(s)
    tabs = {}
    for ws in sh.worksheets():
        tabs[ws.title] = (ws, ws.get_all_values())
    store = Store(data_dir)
    names = store.names()
    foreign = set()
    for t, (_ws, vals) in tabs.items():
        if t not in names and not _blank(vals):
            names.append(t)
            if not _is_app_tab(vals):
                foreign.add(t)
    for n in store.names():
        if n != cur_name and store.load(n).get("sheet_readonly"):
            foreign.add(n)
    if cur_name in cur_ro:
        foreign.add(cur_name)
    done = []
    total_items = 0
    for i, name in enumerate(names, 1):
        q.put(("progress", i, len(names), f"スプレッドシート同期 ({i}/{len(names)}) {name}"))
        ws, vals = tabs.get(name, (None, []))
        if name == cur_name:
            items, deleted = cur_items, cur_deleted
        elif name in store.names():
            d = store.load(name)
            items, deleted = d["items"], d.get("deleted", {})
        else:
            items, deleted = [], {}
        ro = name in foreign
        if ro:
            upd, new = pull_foreign(vals, name, items)
            syncs = {}
        else:
            upd, new, syncs = sync_one(sh, ws, vals, name, items, deleted)
        total_items += len(items) + len(new)
        if name == cur_name:
            q.put(("sheet_apply", upd, new, syncs))
        else:
            if name in store.names():
                d = store.load(name)
            else:
                d = {"name": name, "items": [], "deleted": {}}
            apply_sheet_result(d["items"], upd, new, syncs)
            if ro:
                d["sheet_readonly"] = True
            store.save(name, d, merge=False)
        done.append(name)
    # 空の初期シート(シート1 / Sheet1)は、同期した一覧がある場合のみ片付ける
    if done:
        for t, (ws, vals) in tabs.items():
            if t in ("シート1", "Sheet1") and _blank(vals) and t not in done:
                try:
                    sh.del_worksheet(ws)
                except Exception:  # noqa
                    pass
    q.put(("status", f"スプレッドシート同期完了: {len(done)} 一覧 / {total_items} 件"))


def job_sheet_rename(s, old, new, q):
    sh = sheet_open(s)
    for ws in sh.worksheets():
        if ws.title == old:
            ws.update_title(new)
            return


def job_sheet_delete(s, name, q):
    sh = sheet_open(s)
    for ws in sh.worksheets():
        if ws.title == name and _is_app_tab(ws.get_all_values()):
            sh.del_worksheet(ws)
            return


def job_sheet_dups(s, items, thr, q):
    """スプレッドシート(全シート)の内容と、現在の一覧の重複を検索する。"""
    q.put(("status", "スプレッドシートを読み込み中…"))
    sh = sheet_open(s)
    local_ids = {it["id"] for it in items}
    recs = []
    for ws in sh.worksheets():
        vals = ws.get_all_values()
        if len(vals) < 2:
            continue
        hdr = [h.strip().lower() for h in vals[0]]

        def col(names):
            for n in names:
                if n in hdr:
                    return hdr.index(n)
            return None
        ti = col(["タイトル", "title", "名前", "作品名", "作品", "ファイル名", "題名", "name"])
        ti = 0 if ti is None else ti
        pi, gi, ii = col(["パス", "path"]), col(["グループ", "group"]), col(["id"])

        def cell(r, i):
            return r[i].strip() if i is not None and i < len(r) else ""
        for n, r in enumerate(vals[1:], 2):
            title = cell(r, ti)
            if not title or (ii is not None and cell(r, ii) in local_ids):
                continue
            recs.append({"sheet": ws.title, "row": n, "title": title, "path": cell(r, pi), "group": cell(r, gi)})
    exact = defaultdict(list)
    bypath = defaultdict(list)
    for r in recs:
        r["k"] = normalize_title(r["title"])
        r["e"] = re.sub(r"\s+", "", unicodedata.normalize("NFKC", r["title"]).lower())
        exact[r["e"]].append(r)
        if r["path"]:
            bypath[os.path.normcase(r["path"])].append(r)
    out = {}
    sm = difflib.SequenceMatcher(None, autojunk=False)
    total = len(items)
    for i, it in enumerate(items):
        if i % 10 == 0:
            q.put(("progress", i, total, f"スプレッドシートと照合中 ({i}/{total})"))
        fl, seen = [], set()

        def add(r, kind, score):
            key = (r["sheet"], r["row"])
            if key in seen:
                return
            seen.add(key)
            fl.append({"id": f"sheet:{r['sheet']}:{r['row']}", "kind": kind, "score": round(score, 3), "sheet": True,
                       "name": f"[{r['sheet']}] {r['title']}", "path": f"シート「{r['sheet']}」 {r['row']}行目 {r['path']}".strip()})
        for r in bypath.get(os.path.normcase(it["path"]), []):
            add(r, "same", 1.0)
        e = re.sub(r"\s+", "", unicodedata.normalize("NFKC", it["title"]).lower())
        for r in exact.get(e, []):
            add(r, "same", 1.0)
        k = normalize_title(it["title"])
        if len(k) >= 3:
            sm.set_seq2(k)
            for r in recs:
                if len(r["k"]) < 3 or (it["group"] and it["group"] == r["group"]):
                    continue
                sm.set_seq1(r["k"])
                if sm.real_quick_ratio() < thr or sm.quick_ratio() < thr:
                    continue
                sc = sm.ratio()
                if sc >= thr:
                    add(r, "similar", sc)
        fl.sort(key=lambda f: (f["kind"] != "same", -f["score"]))
        out[it["id"]] = fl[:8]
    q.put(("sheet_flags", out, len(recs)))


# ----------------------------------------------------------------- ダイアログ
class PickDialog(tk.Toplevel):
    def __init__(self, parent, title, label, values, initial="", editable=True):
        super().__init__(parent)
        self.title(title)
        self.result = None
        self.transient(parent)
        self.resizable(False, False)
        ttk.Label(self, text=label).pack(padx=12, pady=(12, 4), anchor="w")
        self.var = tk.StringVar(value=initial)
        self.cb = ttk.Combobox(self, textvariable=self.var, values=values, width=40,
                               state="normal" if editable else "readonly")
        self.cb.pack(padx=12, pady=4)
        fr = ttk.Frame(self)
        fr.pack(pady=10)
        ttk.Button(fr, text="OK", command=self.ok).pack(side="left", padx=6)
        ttk.Button(fr, text="キャンセル", command=self.destroy).pack(side="left", padx=6)
        self.bind("<Return>", lambda e: self.ok())
        self.bind("<Escape>", lambda e: self.destroy())
        self.cb.focus_set()
        self.grab_set()
        self.wait_window()

    def ok(self):
        self.result = self.var.get().strip()
        self.destroy()


class SettingsDialog(tk.Toplevel):
    def __init__(self, parent, s):
        super().__init__(parent)
        self.title("設定")
        self.transient(parent)
        self.result = None
        self.dir = tk.StringVar(value=s["data_dir"])
        self.mode = tk.IntVar(value=s["thumb_mode"])
        self.hash = tk.StringVar(value=s["hash_mode"])
        self.thr = tk.DoubleVar(value=s["sim_threshold"])
        pad = {"padx": 12, "pady": 4}
        ttk.Label(self, text="データ保存先 (Googleドライブの同期フォルダ内を指定)").pack(anchor="w", **pad)
        fr = ttk.Frame(self)
        fr.pack(fill="x", **pad)
        ttk.Entry(fr, textvariable=self.dir, width=52).pack(side="left", fill="x", expand=True)
        ttk.Button(fr, text="参照", command=self.browse).pack(side="left", padx=4)
        ttk.Label(self, text="サムネイル").pack(anchor="w", **pad)
        fr = ttk.Frame(self)
        fr.pack(anchor="w", **pad)
        ttk.Radiobutton(fr, text="1コマ", variable=self.mode, value=1).pack(side="left", padx=6)
        ttk.Radiobutton(fr, text="4コマ", variable=self.mode, value=4).pack(side="left", padx=6)
        ttk.Label(self, text="同一動画の判定(ハッシュ)").pack(anchor="w", **pad)
        ttk.Radiobutton(self, text="高速: 先頭/中央/末尾 各1MB + サイズ (おすすめ・NASでも速い)",
                        variable=self.hash, value="quick").pack(anchor="w", padx=24)
        ttk.Radiobutton(self, text="厳密: ファイル全体 (サイズが同じ動画のみ・非常に遅い場合あり)",
                        variable=self.hash, value="full").pack(anchor="w", padx=24)
        ttk.Label(self, text="類似判定のしきい値 (0.5〜1.0 / 大きいほど厳しい)").pack(anchor="w", **pad)
        ttk.Spinbox(self, from_=0.5, to=1.0, increment=0.05, textvariable=self.thr,
                    width=6, format="%.2f").pack(anchor="w", padx=24)
        ttk.Label(self, text="パス対応 (端末ごとにNASのパスが違う場合のみ / 1行に「データ内のパス=この端末のパス」)").pack(anchor="w", **pad)
        self.pm = tk.Text(self, width=60, height=3)
        self.pm.pack(padx=12)
        self.pm.insert("1.0", "\n".join(f"{a}={b}" for a, b in s.get("path_map", [])))
        ttk.Label(self, text="スプレッドシート連携 (Google Sheets API / pip install gspread)").pack(anchor="w", **pad)
        self.sheet = tk.StringVar(value=s.get("sheet_url", ""))
        ttk.Entry(self, textvariable=self.sheet, width=62).pack(padx=12)
        ttk.Label(self, text="↑ スプレッドシートのURL / 下: client_secret.json(OAuth)またはサービスアカウントのJSON").pack(anchor="w", padx=12)
        self.sa = tk.StringVar(value=s.get("sa_json", ""))
        fr = ttk.Frame(self)
        fr.pack(fill="x", **pad)
        ttk.Entry(fr, textvariable=self.sa, width=52).pack(side="left", fill="x", expand=True)
        ttk.Button(fr, text="JSON参照", command=self.browse_sa).pack(side="left", padx=4)
        self.auto = tk.BooleanVar(value=s.get("sheet_auto", False))
        ttk.Checkbutton(self, text="変更後に自動でスプレッドシートへ同期する(約1分ごと)", variable=self.auto).pack(anchor="w", padx=12)
        fr = ttk.Frame(self)
        fr.pack(pady=12)
        ttk.Button(fr, text="OK", command=self.ok).pack(side="left", padx=6)
        ttk.Button(fr, text="キャンセル", command=self.destroy).pack(side="left", padx=6)
        self.grab_set()
        self.wait_window()

    def browse(self):
        d = filedialog.askdirectory(parent=self, title="データ保存先フォルダ")
        if d:
            self.dir.set(os.path.normpath(d))

    def browse_sa(self):
        f = filedialog.askopenfilename(parent=self, title="サービスアカウントのJSONキー",
                                       filetypes=[("JSON", "*.json"), ("すべて", "*.*")])
        if f:
            self.sa.set(os.path.normpath(f))

    def ok(self):
        try:
            thr = min(1.0, max(0.5, float(self.thr.get())))
        except (tk.TclError, ValueError):
            thr = 0.8
        self.result = {"data_dir": self.dir.get().strip(), "thumb_mode": self.mode.get(),
                       "hash_mode": self.hash.get(), "sim_threshold": thr,
                       "path_map": parse_pmap(self.pm.get("1.0", "end")),
                       "sheet_url": self.sheet.get().strip(), "sa_json": self.sa.get().strip(),
                       "sheet_auto": bool(self.auto.get())}
        self.destroy()


# ----------------------------------------------------------------- メインUI
class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("動画カタログ")
        self.geometry("1280x760")
        self.option_add("*Font", ("Yu Gothic UI", 10))
        ttk.Style(self).configure("Treeview", rowheight=24, font=("Yu Gothic UI", 10))
        self.settings = load_settings()
        self.q = queue.Queue()
        self.busy = False
        self.photo = None
        self.cur_name = None
        self.data = {"items": []}
        self.by_id = {}
        self.open_groups = set()
        self.store = None
        self.move_errs = []
        self.job_kind = ""
        self.sheet_dirty = False
        self.build_ui()
        self.open_store()
        self.after(100, self.poll)
        self.after(5000, self.watch_external)
        self.after(60000, self.auto_sheet)
        publish_app(self.settings["data_dir"])
        self.protocol("WM_DELETE_WINDOW", self.destroy)

    # ---- UI構築
    def build_ui(self):
        top = ttk.Frame(self)
        top.pack(fill="x", padx=8, pady=6)
        ttk.Label(top, text="一覧:").pack(side="left")
        self.list_var = tk.StringVar()
        self.list_cb = ttk.Combobox(top, textvariable=self.list_var, state="readonly", width=20)
        self.list_cb.pack(side="left", padx=4)
        self.list_cb.bind("<<ComboboxSelected>>", lambda e: self.switch_list(self.list_var.get()))
        for text, cmd in (("＋追加", self.add_list), ("名前変更", self.rename_list), ("－削除", self.delete_list)):
            ttk.Button(top, text=text, command=cmd, width=8).pack(side="left", padx=2)
        ttk.Separator(top, orient="vertical").pack(side="left", fill="y", padx=8)
        ttk.Button(top, text="📁 フォルダ読込", command=self.import_folder).pack(side="left", padx=2)
        ttk.Button(top, text="重複チェック", command=self.recheck).pack(side="left", padx=2)
        ttk.Button(top, text="サムネ再作成", command=self.regen_thumbs).pack(side="left", padx=2)
        ttk.Separator(top, orient="vertical").pack(side="left", fill="y", padx=8)
        ttk.Button(top, text="📊 スプシ同期", command=self.sheet_sync).pack(side="left", padx=2)
        ttk.Button(top, text="スプシと重複検索", command=self.sheet_dups).pack(side="left", padx=2)
        ttk.Button(top, text="⚙ 設定", command=self.open_settings).pack(side="right")
        self.side_btn = ttk.Button(top, text="▶ 詳細パネルを隠す (F4)", command=self.toggle_side)
        self.side_btn.pack(side="right", padx=4)
        self.bind("<F4>", lambda e: self.toggle_side())

        bar = ttk.Frame(self)
        bar.pack(fill="x", padx=8, pady=(0, 6))
        ttk.Label(bar, text="検索:").pack(side="left")
        self.q_var = tk.StringVar()
        ttk.Entry(bar, textvariable=self.q_var, width=34).pack(side="left", padx=4)
        ttk.Label(bar, text="ジャンル:").pack(side="left", padx=(12, 0))
        self.g_var = tk.StringVar(value="すべて")
        self.g_cb = ttk.Combobox(bar, textvariable=self.g_var, state="readonly", width=16)
        self.g_cb.pack(side="left", padx=4)
        self.flag_only = tk.BooleanVar()
        ttk.Checkbutton(bar, text="同一・類似のみ", variable=self.flag_only,
                        command=self.refresh_tree).pack(side="left", padx=12)
        self.count_lbl = ttk.Label(bar, text="")
        self.count_lbl.pack(side="right")
        self.q_var.trace_add("write", lambda *a: self.refresh_tree())
        self.g_cb.bind("<<ComboboxSelected>>", lambda e: self.refresh_tree())

        body = ttk.PanedWindow(self, orient="horizontal")
        body.pack(fill="both", expand=True, padx=8)
        left = ttk.Frame(body)
        body.add(left, weight=1)
        cols = ("genre", "count", "dur", "size", "flag", "path")
        self.tree = ttk.Treeview(left, columns=cols, selectmode="extended")
        heads = {"#0": ("タイトル / グループ", 300), "genre": ("ジャンル", 90), "count": ("話数", 50),
                 "dur": ("時間", 70), "size": ("サイズ", 70), "flag": ("同一・類似", 260), "path": ("パス", 300)}
        for c, (t, w) in heads.items():
            self.tree.heading(c, text=t)
            w = int(self.settings.get("col_widths", {}).get(c, w))
            # stretch=False: 列幅を広げても他の列が自動で縮まない(広げたまま保持)
            self.tree.column(c, width=w, minwidth=40, anchor="w", stretch=False)
        self.tree.tag_configure("same", background="#ffd0d0")
        self.tree.tag_configure("similar", background="#fff1b8")
        self.tree.tag_configure("group", font=("Yu Gothic UI", 10, "bold"))
        sb = ttk.Scrollbar(left, command=self.tree.yview)
        hsb = ttk.Scrollbar(left, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=sb.set, xscrollcommand=hsb.set)
        left.rowconfigure(0, weight=1)
        left.columnconfigure(0, weight=1)
        self.tree.grid(row=0, column=0, sticky="nsew")
        sb.grid(row=0, column=1, sticky="ns")
        hsb.grid(row=1, column=0, sticky="ew")
        self.tree.bind("<ButtonRelease-1>", lambda e: self.after_idle(self.save_col_widths), add="+")
        self.tree.bind("<<TreeviewSelect>>", self.on_select)
        self.tree.bind("<Double-1>", self.on_double)
        self.tree.bind("<Button-3>", self.on_right)
        self.tree.bind("<Delete>", lambda e: self.remove_selected())

        right = ttk.Frame(body, width=int(self.settings.get("side_w", 300)))
        self.body, self.right = body, right
        self.thumb_w, self.thumb_it = 280, None
        if self.settings.get("side_show", True):
            body.add(right, weight=0)
        if not self.settings.get("side_show", True):
            self.side_btn.config(text="◀ 詳細パネルを表示 (F4)")
        right.bind("<Configure>", self.on_side_resize)
        self._side_init = body.bind("<Configure>", self._first_layout, add="+")
        body.bind("<ButtonRelease-1>", lambda e: self.after_idle(self.save_side_w), add="+")
        self.thumb_lbl = ttk.Label(right, text="(サムネイルなし)", anchor="center")
        self.thumb_lbl.pack(fill="x", pady=(0, 6))
        self.detail = tk.Text(right, wrap="word", height=20, state="disabled", relief="flat",
                              bg=self.cget("bg"), font=("Yu Gothic UI", 10))
        self.detail.pack(fill="both", expand=True)
        self.detail.tag_configure("h", font=("Yu Gothic UI", 10, "bold"))
        self.detail.tag_configure("hl", background="#ffb347")
        self.detail.tag_configure("same_t", foreground="#b00020", font=("Yu Gothic UI", 10, "bold"))
        self.detail.tag_configure("sim_t", foreground="#9a6a00", font=("Yu Gothic UI", 10, "bold"))
        self.detail.tag_configure("link", foreground="#0b57d0", underline=True)

        self.menu = tk.Menu(self, tearoff=0)
        for text, cmd in (("ジャンルを設定…", self.set_genre), ("グループを設定/解除…", self.set_group),
                          ("別の一覧へ移動…", self.move_to_list),
                          ("ファイルを別フォルダへ移動…", self.move_files), (None, None),
                          ("ファイルを開く", self.open_file), ("フォルダを開く", self.open_folder), (None, None),
                          ("一覧から削除 (ファイルは消えません)", self.remove_selected)):
            if text is None:
                self.menu.add_separator()
            else:
                self.menu.add_command(label=text, command=cmd)

        st = ttk.Frame(self)
        st.pack(fill="x", padx=8, pady=6)
        self.status = ttk.Label(st, text="準備完了")
        self.status.pack(side="left")
        self.pb = ttk.Progressbar(st, length=260, mode="determinate")
        self.pb.pack(side="right")

    # ---- ストア / 一覧
    def open_store(self):
        try:
            self.store = Store(self.settings["data_dir"])
        except OSError as e:
            messagebox.showerror("エラー", f"データ保存先を開けません:\n{self.settings['data_dir']}\n{e}")
            self.store = Store(os.path.join(os.path.expanduser("~"), "Documents", APP))
            self.settings["data_dir"] = self.store.root
        names = self.store.names()
        if not names:
            self.store.create("マイ一覧")
            names = ["マイ一覧"]
        self.list_cb["values"] = names
        self.switch_list(self.cur_name if self.cur_name in names else names[0])

    def switch_list(self, name):
        if self.busy:
            self.list_var.set(self.cur_name or "")
            return
        self.cur_name = name
        self.list_var.set(name)
        self.list_cb["values"] = self.store.names()
        self.data = self.store.load(name)
        self.after_data_change(save=False)

    def after_data_change(self, save=True):
        if save:
            self.store.save(self.cur_name, self.data)
            self.sheet_dirty = True
        self.by_id = {it["id"]: it for it in self.data["items"]}
        gs = sorted({it["genre"] for it in self.data["items"] if it["genre"]})
        self.g_cb["values"] = ["すべて", "(未設定)"] + gs
        if self.g_var.get() not in self.g_cb["values"]:
            self.g_var.set("すべて")
        self.refresh_tree()

    def add_list(self):
        if self.busy:
            return
        v = PickDialog(self, "一覧を追加", "新しい一覧の名前 (例: ドラマ, 映画, 趣味)", [], "").result
        if not v:
            return
        if not self.store.valid_name(v) or v in self.store.names():
            messagebox.showwarning("追加できません", "名前が空・重複、または使えない文字が含まれています。")
            return
        self.store.create(v)
        self.switch_list(v)

    def rename_list(self):
        if self.busy:
            return
        v = PickDialog(self, "名前変更", "新しい名前", [], self.cur_name).result
        if not v or v == self.cur_name:
            return
        if not self.store.valid_name(v) or v in self.store.names():
            messagebox.showwarning("変更できません", "名前が空・重複、または使えない文字が含まれています。")
            return
        old = self.cur_name
        self.store.rename(old, v)
        self.switch_list(v)
        if self.sheet_ready():
            self.run_job(job_sheet_rename, self.settings, old, v)

    def delete_list(self):
        if self.busy:
            return
        if len(self.store.names()) <= 1:
            messagebox.showinfo("削除できません", "最後の一覧は削除できません。")
            return
        n = len(self.data["items"])
        if not messagebox.askyesno("一覧の削除", f"一覧「{self.cur_name}」({n}件)を削除します。\n"
                                   "動画ファイル自体は削除されません。"
                                   + ("\nスプレッドシートの同名シートも削除されます。" if self.sheet_ready() else "")
                                   + "\nよろしいですか?"):
            return
        old = self.cur_name
        self.store.delete(old)
        self.switch_list(self.store.names()[0])
        if self.sheet_ready():
            self.run_job(job_sheet_delete, self.settings, old)

    # ---- 読み込み / ジョブ
    def run_job(self, fn, *args):
        if self.busy:
            messagebox.showinfo("処理中", "別の処理が実行中です。完了までお待ちください。")
            return
        self.busy = True
        self.job_kind = fn.__name__
        self.list_cb.configure(state="disabled")

        def target():
            try:
                fn(*args, self.q)
            except Exception as e:  # noqa
                self.q.put(("error", repr(e)))
            finally:
                self.q.put(("done",))
        threading.Thread(target=target, daemon=True).start()

    def pmap(self):
        return [tuple(x) for x in self.settings.get("path_map", [])]

    def lpath(self, it):
        return to_local(it["path"], self.pmap())

    def snapshot(self):
        pm = self.pmap()
        return [dict(it, lpath=to_local(it["path"], pm)) for it in self.data["items"]]

    def watch_external(self):
        """他の端末がGoogleドライブ経由で更新したら自動で反映する。"""
        try:
            if not self.busy and self.store and self.cur_name:
                names = self.store.names()
                if list(self.list_cb["values"]) != names:
                    self.list_cb["values"] = names
                if self.cur_name not in names:
                    self.switch_list(names[0])
                elif self.store.changed_externally(self.cur_name):
                    self.data = self.store.load(self.cur_name)
                    self.after_data_change(save=False)
                    self.status.config(text="他の端末の変更を反映しました")
        except (OSError, ValueError):
            pass
        self.after(5000, self.watch_external)

    def save_col_widths(self):
        w = {c: int(self.tree.column(c, "width")) for c in ("#0",) + tuple(self.tree["columns"])}
        if w != self.settings.get("col_widths"):
            self.settings["col_widths"] = w
            try:
                save_settings(self.settings)
            except OSError:
                pass

    def sheet_ready(self):
        return bool(self.settings.get("sheet_url") and self.settings.get("sa_json"))

    def sheet_sync(self, auto=False):
        if self.busy:
            return
        s = self.settings
        if not s.get("sheet_url") or not s.get("sa_json"):
            if not auto:
                messagebox.showinfo("スプレッドシート", "先に 設定 でスプレッドシートのURLとサービスアカウントJSONを指定してください。")
            return
        self.sheet_dirty = False
        self.run_job(job_sheet_sync, s, self.cur_name, self.snapshot(), dict(self.data.get("deleted", {})),
                     self.store.root, {self.cur_name} if self.data.get("sheet_readonly") else set())

    def sheet_dups(self):
        if self.busy:
            return
        s = self.settings
        if not s.get("sheet_url") or not s.get("sa_json"):
            messagebox.showinfo("スプレッドシート", "先に 設定 でスプレッドシートのURLとサービスアカウントJSONを指定してください。")
            return
        self.run_job(job_sheet_dups, s, self.snapshot(), s["sim_threshold"])

    def auto_sheet(self):
        if self.settings.get("sheet_auto") and self.sheet_dirty and not self.busy:
            self.sheet_sync(auto=True)
        self.after(60000, self.auto_sheet)

    def move_files(self):
        items = self.selected_items()
        if not items or self.busy:
            return
        d = filedialog.askdirectory(parent=self, title=f"{len(items)} 件の移動先フォルダを選択")
        if not d:
            return
        d = os.path.normpath(d)
        r = messagebox.askyesnocancel(
            "ファイルの移動",
            f"{len(items)} 件の動画ファイルを実際に移動します。\n移動先: {d}\n\n"
            "あわせてグループ名を移動先のフォルダ名に変更しますか?\n"
            "はい: グループも変更 / いいえ: グループはそのまま / キャンセル: 移動しない")
        if r is None:
            return
        self.move_errs = []
        self.run_job(job_move, [(it["id"], self.lpath(it)) for it in items], d, r, self.pmap())

    def import_folder(self):
        if self.busy:
            return
        d = filedialog.askdirectory(parent=self, title="動画フォルダ(NAS)を選択")
        if not d:
            return
        d = os.path.normpath(d)
        grp = messagebox.askyesno(
            "グループ化",
            "選択したフォルダ直下の動画も、フォルダ名でまとめますか?\n\n"
            "はい: 1作品(ドラマ等)のフォルダを選んだ場合\n"
            "いいえ: 作品フォルダが並ぶ親フォルダを選んだ場合\n\n"
            "※ サブフォルダ内に2本以上の動画があれば、そのフォルダ名で自動的にまとめます。")
        s = self.settings
        self.run_job(job_scan, d, grp, self.snapshot(), s["thumb_mode"], s["hash_mode"],
                     s["sim_threshold"], self.store.thumbs_dir, self.pmap())

    def recheck(self):
        s = self.settings
        self.run_job(job_analyze, self.snapshot(), s["hash_mode"], s["sim_threshold"])

    def regen_thumbs(self, force=True):
        s = self.settings
        items = self.snapshot()
        if not items:
            return
        self.run_job(job_thumbs, items, s["thumb_mode"], self.store.thumbs_dir, force)

    def poll(self):
        changed = False
        sync_done = False
        try:
            while True:
                m = self.q.get_nowait()
                k = m[0]
                if k == "status":
                    self.status.config(text=m[1])
                elif k == "progress":
                    _, cur, total, text = m
                    self.pb.configure(maximum=max(total, 1), value=cur)
                    self.status.config(text=text)
                elif k == "items":
                    self.data["items"].extend({k: v for k, v in it.items() if k != "lpath"} for it in m[1])
                    changed = True
                    self.status.config(text=f"{len(m[1])} 件を追加 (動画 {m[2]} 本を検出)")
                elif k == "thumb":
                    it = self.by_id.get(m[1]) or next((x for x in self.data["items"] if x["id"] == m[1]), None)
                    if it:
                        if m[2]:
                            it["duration"] = m[2]
                        it["thumb"], it["thumb_mode"] = m[3], m[4]
                elif k == "moved":
                    it = self.by_id.get(m[1])
                    if it:
                        it["path"] = m[2]
                        if m[3] is not None:
                            it["group"] = m[3]
                        changed = True
                elif k == "move_err":
                    self.move_errs.append(m[1])
                elif k == "sheet_apply":
                    apply_sheet_result(self.data["items"], m[1], m[2], m[3])
                    changed = True
                elif k == "sheet_flags":
                    for it in self.data["items"]:
                        old = [f for f in it.get("flags", []) if not f.get("sheet")]
                        it["flags"] = old + m[1].get(it["id"], [])
                    changed = True
                    self.status.config(text=f"スプレッドシート {m[2]} 行と照合しました")
                elif k == "flags":
                    flags, newhash = m[1], m[2]
                    for it in self.data["items"]:
                        it["flags"] = flags.get(it["id"], []) + [f for f in it.get("flags", []) if f.get("sheet")]
                        if it["id"] in newhash:
                            hk, hv = newhash[it["id"]]
                            it[hk] = hv
                    changed = True
                elif k == "error":
                    messagebox.showerror("エラー", m[1])
                elif k == "done":
                    self.busy = False
                    self.list_cb.configure(state="readonly")
                    self.pb.configure(value=0)
                    nf = sum(1 for it in self.data["items"] if it.get("flags"))
                    if self.job_kind not in ("job_sheet_sync", "job_move", "job_sheet_dups", "job_sheet_rename", "job_sheet_delete"):
                        self.status.config(text=f"完了 — 同一/類似の疑い: {nf} 件")
                    changed = True
                    if self.move_errs:
                        messagebox.showwarning("移動できなかったファイル", "\n".join(self.move_errs[:20]))
                        self.move_errs = []
                    if self.job_kind == "job_move":
                        self.status.config(text="ファイルの移動が完了しました")
                    if self.job_kind == "job_sheet_sync":
                        sync_done = True
                        self.list_cb["values"] = self.store.names()
        except queue.Empty:
            pass
        if changed:
            self.after_data_change()
            if sync_done:
                self.sheet_dirty = False
        self.after(150, self.poll)

    # ---- ツリー表示
    def refresh_tree(self):
        for iid in self.tree.get_children():
            if iid.startswith("g:"):
                (self.open_groups.add if self.tree.item(iid, "open") else self.open_groups.discard)(iid)
        self.tree.delete(*self.tree.get_children())
        terms = unicodedata.normalize("NFKC", self.q_var.get()).lower().split()
        genre = self.g_var.get()
        shown = 0
        groups, singles = defaultdict(list), []
        for it in self.data["items"]:
            hay = unicodedata.normalize("NFKC", " ".join(
                [it["title"], it["group"], it["genre"], it["path"]])).lower()
            if any(t not in hay for t in terms):
                continue
            if genre == "(未設定)" and it["genre"]:
                continue
            if genre not in ("すべて", "(未設定)") and it["genre"] != genre:
                continue
            if self.flag_only.get() and not it.get("flags"):
                continue
            (groups[it["group"]] if it["group"] else singles).append(it)
            shown += 1
        rows = [(g, "g", v) for g, v in groups.items()] + [(it["title"], "i", it) for it in singles]
        rows.sort(key=lambda r: natural_key(r[0]))
        searching = bool(terms) or self.flag_only.get() or genre != "すべて"
        for name, kind, obj in rows:
            if kind == "i":
                self.insert_item("", obj)
                continue
            members = sorted(obj, key=lambda x: natural_key(x["title"]))
            gen = {m["genre"] for m in members}
            kinds = {f["kind"] for m in members for f in m.get("flags", [])}
            tag = ("same" if "same" in kinds else "similar" if kinds else "", "group")
            nflag = sum(1 for m in members if m.get("flags"))
            iid = "g:" + name
            self.tree.insert("", "end", iid=iid, text="📂 " + name, tags=tag, open=(iid in self.open_groups or searching),
                             values=(gen.pop() if len(gen) == 1 else "(混在)", len(members),
                                     fmt_dur(sum(m["duration"] for m in members)),
                                     fmt_size(sum(m["size"] for m in members)),
                                     f"⚠ {nflag} 件に同一/類似あり" if nflag else "", ""))
            for m in members:
                self.insert_item(iid, m)
        self.count_lbl.config(text=f"{shown} / {len(self.data['items'])} 件")
        self.show_detail()

    def flag_text(self, it):
        fl = it.get("flags") or []
        if not fl:
            return ""
        f = fl[0]
        s = ("【同一】" if f["kind"] == "same" else f"【類似{int(f['score'] * 100)}%】") + f["name"]
        return s + (f"  他{len(fl) - 1}件" if len(fl) > 1 else "")

    def insert_item(self, parent, it):
        fl = it.get("flags") or []
        tag = ("same",) if any(f["kind"] == "same" for f in fl) else ("similar",) if fl else ()
        self.tree.insert(parent, "end", iid=it["id"], text=("🎞 " if not parent else "") + it["title"], tags=tag,
                         values=(it["genre"], "", fmt_dur(it["duration"]), fmt_size(it["size"]),
                                 self.flag_text(it), it["path"]))

    # ---- 選択 / 詳細
    def selected_items(self):
        out, seen = [], set()
        for iid in self.tree.selection():
            ids = [c for c in self.tree.get_children(iid)] if iid.startswith("g:") else [iid]
            for i in ids:
                if i in self.by_id and i not in seen:
                    seen.add(i)
                    out.append(self.by_id[i])
        return out

    def on_select(self, _e=None):
        self.show_detail()

    def write(self, text, *tags):
        self.detail.insert("end", text, tags)

    def write_hl(self, s, blocks, which):
        pos = 0
        for b in blocks:
            start = b.a if which == 0 else b.b
            if b.size < 2:
                continue
            if start > pos:
                self.write(s[pos:start])
            self.write(s[start:start + b.size], "hl")
            pos = start + b.size
        self.write(s[pos:])

    def show_detail(self):
        sel = self.tree.selection()
        self.detail.configure(state="normal")
        self.detail.delete("1.0", "end")
        for t in list(self.detail.tag_names()):
            if t.startswith("lnk"):
                self.detail.tag_delete(t)
        if not sel:
            self.thumb_lbl.configure(image="", text="(サムネイルなし)")
            self.photo = None
            self.detail.configure(state="disabled")
            return
        iid = sel[0]
        if iid.startswith("g:"):
            members = self.selected_items()[: len(self.tree.get_children(iid))]
            self.write(iid[2:] + "\n", "h")
            self.write(f"{len(members)} 話 / 合計 {fmt_size(sum(m['size'] for m in members))}\n")
            self.set_thumb(members[0] if members else None)
        else:
            it = self.by_id.get(iid)
            if not it:
                self.detail.configure(state="disabled")
                return
            self.set_thumb(it)
            self.write(it["title"] + "\n", "h")
            self.write(f"ジャンル: {it['genre'] or '(未設定)'}\nグループ: {it['group'] or '(なし)'}\n"
                       f"サイズ: {fmt_size(it['size'])}   時間: {fmt_dur(it['duration']) or '-'}\n"
                       f"パス: {it['path']}\n")
            fl = it.get("flags") or []
            if fl:
                self.write("\n⚠ 同一・類似の疑い (クリックで移動)\n", "h")
            for n, f in enumerate(fl):
                tag = f"lnk{n}"
                if f.get("sheet"):
                    self.write("\n■ スプレッドシートと重複 " + ("(同じタイトル/パス)" if f["kind"] == "same"
                                                         else f"(類似 {int(f['score'] * 100)}%)") + "\n",
                               "same_t" if f["kind"] == "same" else "sim_t")
                    self.write("  → " + f["name"] + "\n")
                elif f["kind"] == "same":
                    self.write("\n■ 同一動画 ", "same_t")
                    self.write("(ファイル内容のハッシュが一致)\n")
                    self.write("  → ", )
                    self.write(f["name"] + "\n", "link", tag)
                else:
                    self.write(f"\n■ 類似動画 {int(f['score'] * 100)}% ", "sim_t")
                    self.write("(橙色の部分が名前で一致)\n")
                    a, b = it["title"], f["name"]
                    blocks = difflib.SequenceMatcher(None, a.lower(), b.lower(), autojunk=False).get_matching_blocks()
                    self.write("  この動画: ")
                    self.write_hl(a, blocks, 0)
                    self.write("\n  相手    : ")
                    self.write_hl(b, blocks, 1)
                    self.write("\n  → ")
                    self.write("相手へ移動\n", "link", tag)
                self.write("  " + f["path"] + "\n")
                self.detail.tag_bind(tag, "<Button-1>", lambda e, i=f["id"]: self.jump_to(i))
                self.detail.tag_bind(tag, "<Enter>", lambda e: self.detail.config(cursor="hand2"))
                self.detail.tag_bind(tag, "<Leave>", lambda e: self.detail.config(cursor=""))
        self.detail.configure(state="disabled")

    def on_side_resize(self, e):
        w = max(120, min(480, e.width - 8))
        if abs(w - self.thumb_w) >= 12:
            self.thumb_w = w
            if self.thumb_it is not None:
                self.set_thumb(self.thumb_it)

    def _first_layout(self, e):
        if e.width > 600:
            self.body.unbind("<Configure>", self._side_init)
            self.after_idle(self.apply_side_w)

    def apply_side_w(self):
        try:
            if str(self.right) in self.body.panes():
                self.body.sashpos(0, max(300, self.body.winfo_width() - int(self.settings.get("side_w", 300))))
        except tk.TclError:
            pass

    def save_side_w(self):
        if str(self.right) in self.body.panes():
            w = self.right.winfo_width()
            if w > 100 and w != self.settings.get("side_w"):
                self.settings["side_w"] = w
                try:
                    save_settings(self.settings)
                except OSError:
                    pass

    def toggle_side(self):
        show = str(self.right) not in self.body.panes()
        if show:
            self.body.add(self.right, weight=0)
            self.update_idletasks()
            self.apply_side_w()
        else:
            self.body.forget(self.right)
        self.settings["side_show"] = show
        self.side_btn.config(text="◀ 詳細パネルを表示 (F4)" if not show else "▶ 詳細パネルを隠す (F4)")
        try:
            save_settings(self.settings)
        except OSError:
            pass

    def set_thumb(self, it):
        self.thumb_it = it
        p = os.path.join(self.store.thumbs_dir, it["thumb"]) if it and it.get("thumb") else ""
        try:
            im = Image.open(p)
            im.thumbnail((self.thumb_w, int(self.thumb_w * 9 / 16)))
            self.photo = ImageTk.PhotoImage(im)
            self.thumb_lbl.configure(image=self.photo, text="")
        except Exception:
            self.photo = None
            self.thumb_lbl.configure(image="", text="(サムネイルなし)")

    def jump_to(self, iid):
        if iid not in self.by_id:
            return
        if not self.tree.exists(iid):
            self.q_var.set("")
            self.g_var.set("すべて")
            self.flag_only.set(False)
            self.refresh_tree()
        if not self.tree.exists(iid):
            return
        par = self.tree.parent(iid)
        if par:
            self.tree.item(par, open=True)
            self.open_groups.add(par)
        self.tree.selection_set(iid)
        self.tree.focus(iid)
        self.tree.see(iid)

    def on_double(self, e):
        if self.tree.identify_region(e.x, e.y) == "tree" or self.tree.identify_row(e.y):
            iid = self.tree.identify_row(e.y)
            if iid and not iid.startswith("g:"):
                self.open_file()

    def on_right(self, e):
        iid = self.tree.identify_row(e.y)
        if iid:
            if iid not in self.tree.selection():
                self.tree.selection_set(iid)
            self.menu.tk_popup(e.x_root, e.y_root)

    # ---- 編集操作
    def all_genres(self):
        return sorted(set(DEFAULT_GENRES) | {it["genre"] for it in self.data["items"] if it["genre"]})

    def set_genre(self):
        items = self.selected_items()
        if not items or self.busy:
            return
        cur = items[0]["genre"]
        v = PickDialog(self, "ジャンル設定", f"{len(items)} 件のジャンル (空欄で未設定に戻す)", self.all_genres(), cur).result
        if v is None:
            return
        for it in items:
            it["genre"] = v
        self.after_data_change()

    def set_group(self):
        items = self.selected_items()
        if not items or self.busy:
            return
        groups = sorted({it["group"] for it in self.data["items"] if it["group"]})
        v = PickDialog(self, "グループ設定", f"{len(items)} 件をまとめるグループ名 (空欄でグループ解除)",
                       groups, items[0]["group"]).result
        if v is None:
            return
        for it in items:
            it["group"] = v
        self.after_data_change()

    def move_to_list(self):
        items = self.selected_items()
        others = [n for n in self.store.names() if n != self.cur_name]
        if not items or self.busy:
            return
        if not others:
            messagebox.showinfo("移動先なし", "先に別の一覧を追加してください。")
            return
        v = PickDialog(self, "一覧へ移動", f"{len(items)} 件の移動先", others, others[0], editable=False).result
        if not v:
            return
        dest = self.store.load(v)
        known = {it["id"] for it in dest["items"]}
        dest["items"].extend(dict(it, flags=[]) for it in items if it["id"] not in known)
        self.store.save(v, dest)
        ids = {it["id"] for it in items}
        self.data["items"] = [it for it in self.data["items"] if it["id"] not in ids]
        for it in self.data["items"]:
            it["flags"] = [f for f in it.get("flags", []) if f["id"] not in ids]
        self.after_data_change()

    def remove_selected(self):
        items = self.selected_items()
        if not items or self.busy:
            return
        if not messagebox.askyesno("一覧から削除", f"{len(items)} 件を一覧から削除します。\n"
                                   "(動画ファイル本体は削除されません)"):
            return
        ids = {it["id"] for it in items}
        self.data["items"] = [it for it in self.data["items"] if it["id"] not in ids]
        for it in self.data["items"]:
            it["flags"] = [f for f in it.get("flags", []) if f["id"] not in ids]
        self.after_data_change()

    def open_file(self):
        its = self.selected_items()
        if its:
            try:
                os.startfile(self.lpath(its[0]))
            except OSError as e:
                messagebox.showerror("開けません", f"{self.lpath(its[0])}\n{e}\n(NASに接続されていますか?\n"
                                     "端末ごとにNASのパスが違う場合は 設定 の「パス対応」を設定してください)")

    def open_folder(self):
        its = self.selected_items()
        if its:
            subprocess.Popen(["explorer", "/select,", os.path.normpath(self.lpath(its[0]))])

    def open_settings(self):
        if self.busy:
            return
        old = dict(self.settings)
        r = SettingsDialog(self, self.settings).result
        if not r:
            return
        self.settings.update(r)
        save_settings(self.settings)
        if r["data_dir"] != old["data_dir"]:
            self.cur_name = None
            self.open_store()
            publish_app(r["data_dir"])
        if r["thumb_mode"] != old["thumb_mode"] and self.data["items"]:
            if messagebox.askyesno("サムネイル", "サムネイル形式が変わりました。今の一覧を作り直しますか?"):
                self.regen_thumbs(force=False)


if __name__ == "__main__":
    App().mainloop()
