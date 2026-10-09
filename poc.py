#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""自治体AI・回答採用アシュアランス 第1弾PoC（単一Python／標準ライブラリのみ）。

  python poc.py                       # 代表6件 + 参考30件 + 補完2件を実行
  python poc.py run --case missing     # 代表ケースを1件だけ実行
  python poc.py complete missing       # HOLD → 合成入力を補完 → 再判定
  python poc.py verify output          # 保存パケットをPythonで再検証
  python poc.py test                   # 回帰・異常入力・変更検出の自己テスト

必須ファイルは本ファイルと cases.json の2つだけ。実AI、実制度、実住民情報、
ネットワーク、形式証明検証器には接続しない。PASSは職員確認用の回答案のみ。
元HTMLの8条件とJSON形式に対応する、範囲を限定した参照実装である。
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import html
import json
import math
import re
import sys
import uuid
from collections import Counter
from datetime import date, datetime, timezone
from decimal import Decimal, ROUND_HALF_UP
from pathlib import Path
from typing import Any, Callable

ROOT = Path(__file__).resolve().parent
VERSION = "1.0.0"
MAX_BYTES = 2 * 1024 * 1024
MAX_SAFE_INTEGER = 9007199254740991
# 受信パケットの自己申告を信頼基準にしない。元HTMLと同じ参照仕様・資料を固定。
# 変更には仕様のレビューと本値の更新が必要。コード自体の認証・改変防止ではない。
REFERENCE_SHA256 = "8e185f953e419889d20347181b3827294ba47353801eb74f68193e7e02a45a14"
ORIGINAL_HTML_SHA256 = "3a52e33171a16e9c44ffff001176838e5a1a43c2a03844990b3c07b4cc60ff7a"
PACKET_SCHEMA = "responsibility-information-packet/demo-1.0"
CANONICALIZATION = "Recursively sorted object keys; array order preserved; JSON primitives; UTF-8; no whitespace"
STATUSES = ("PASS", "HOLD", "REJECT")
TITLES = {"PASS": "回答案として採用可", "HOLD": "職員による追加確認", "REJECT": "この回答案は不採用"}
SCOPE = {
    "data": "fictional_sources_and_synthetic_applicant",
    "method": "deterministic_rules_on_structured_claims",
    "natural_language_inference": False, "formal_proof_checker": False,
    "real_world_validation": False, "administrative_decision": False, "external_send": False,
}
NONCLAIMS = ["No legal compliance certification", "No source or issuer authentication",
             "No real applicant verification", "No production privacy guarantee"]


class InputError(ValueError):
    """受理できない入力。採用判定とは区別し、処理を失敗終了させる。"""


def require(condition: bool, message: str) -> None:
    if not condition:
        raise InputError(message)


def validate_json_tree(value: Any, depth: int = 0) -> None:
    """HTMLと曖昧なく照合するための、限定したJSON数値・Unicode受理域。"""
    require(depth <= 32, "JSONの入れ子が深すぎます。")
    t = type(value)
    if value is None or t is bool:
        return
    if t is int:
        require(abs(value) <= MAX_SAFE_INTEGER, "整数がJavaScriptの安全整数域を超えています。")
    elif t is float:
        # このPoCの小数は補助率（0～1、小数2桁まで）。任意数値のJCS実装ではない。
        require(math.isfinite(value) and 0 <= value <= 1,
                "小数は有限の補助率（0～1）に限定しています。")
        require(Decimal(str(value)).as_tuple().exponent >= -2, "補助率の小数は2桁までです。")
    elif t is str:
        try:
            value.encode("utf-8")
        except UnicodeEncodeError as exc:
            raise InputError("不正なUnicode文字列です。") from exc
    elif t is list:
        require(len(value) <= 2000, "JSON配列が大きすぎます。")
        for item in value:
            validate_json_tree(item, depth + 1)
    elif t is dict:
        require(len(value) <= 2000 and all(type(k) is str for k in value), "JSONオブジェクトが不正です。")
        for k, v in value.items():
            validate_json_tree(k, depth + 1)
            validate_json_tree(v, depth + 1)
    else:
        raise InputError(f"JSONにできない型です：{t.__name__}")


def canonical(value: Any) -> str:
    """元HTMLのcanonicalと同じ表現。受理域はvalidate_json_treeで限定する。"""
    if isinstance(value, dict):
        keys = sorted(value, key=lambda k: k.encode("utf-16-be"))
        return "{" + ",".join(canonical(k) + ":" + canonical(value[k]) for k in keys) + "}"
    if isinstance(value, list):
        return "[" + ",".join(canonical(x) for x in value) + "]"
    if type(value) is float:
        if value == 0:
            return "0"
        text = format(Decimal(str(value)), "f")
        return text.rstrip("0").rstrip(".") if "." in text else text
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), allow_nan=False)


def digest(value: Any) -> str:
    data = value if type(value) is str else canonical(value)
    return hashlib.sha256(data.encode("utf-8")).hexdigest()


def same(a: Any, b: Any) -> bool:
    # Pythonの True == 1 を、JSON上の同一性として誤って採用しない。
    return canonical(a) == canonical(b)


def parse_json(text: str) -> Any:
    def pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in items:
            require(key not in result, f"JSONキーが重複しています：{key}")
            result[key] = value
        return result

    def invalid_constant(value: str) -> Any:
        raise InputError(f"NaN・Infinityは受理しません：{value}")

    try:
        result = json.loads(text.lstrip("\ufeff"), object_pairs_hook=pairs, parse_constant=invalid_constant)
        validate_json_tree(result)
        return result
    except (json.JSONDecodeError, RecursionError, UnicodeError) as exc:
        raise InputError(f"JSONを読み込めません：{exc}") from exc


def read_json(path: Path) -> Any:
    require(path.is_file(), f"ファイルがありません：{path}")
    require(path.stat().st_size <= MAX_BYTES, f"JSONは2MB以下にしてください：{path}")
    return parse_json(path.read_text(encoding="utf-8-sig"))


def write_json(path: Path, value: Any) -> None:
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2, allow_nan=False) + "\n", encoding="utf-8")


def check_keys(value: Any, keys: set[str], where: str) -> None:
    require(type(value) is dict, f"{where}はオブジェクトで指定してください。")
    require(set(value) == keys, f"{where}の項目が不正です。欠落={sorted(keys-set(value))} / 未定義={sorted(set(value)-keys)}")


def string(value: Any, where: str, maximum: int = 2000, nullable: bool = False) -> None:
    if nullable and value is None:
        return
    require(type(value) is str and 0 < len(value) <= maximum, f"{where}は空でない文字列にしてください。")


def iso_date(value: Any, where: str) -> None:
    require(type(value) is str and re.fullmatch(r"[0-9]{4}-[0-9]{2}-[0-9]{2}", value) is not None,
            f"{where}の日付はYYYY-MM-DD形式で指定してください。")
    try:
        require(date.fromisoformat(value).isoformat() == value, f"{where}の日付が不正です。")
    except ValueError as exc:
        raise InputError(f"{where}に存在しない日付が指定されています。") from exc


def worst(values: list[str]) -> str:
    return "REJECT" if "REJECT" in values else "HOLD" if "HOLD" in values else "PASS"


def date_jp(value: str) -> str:
    year, month, day = value.split("-")
    return f"{year}年{int(month)}月{int(day)}日"


def value_label(key: str, value: Any) -> str:
    if key == "max_yen":
        number = (Decimal(value) / 10000).quantize(Decimal("0.001"), rounding=ROUND_HALF_UP)
        text = f"{number:,.3f}".rstrip("0").rstrip(".")
        return text + "万円"
    if key == "rate":
        if value == 0.5:
            return "1/2"
        percent = value * 100
        return (str(int(percent)) if percent == int(percent) else str(percent)) + "%"
    if key == "deadline":
        return date_jp(value)
    if key == "eligibility":
        return {"candidate": "案内上の対象候補", "out_of_scope": "今回の条件では対象外", "needs_review": "条件が未確認"}.get(value, str(value))
    if key == "conditions":
        return f"{len(value)}項目を明示" if isinstance(value, list) else "不明"
    if key == "award_guarantee":
        return "受給・採択を断定" if value else "正式な申請・審査が必要"
    return str(value)


def build_text(claims: dict[str, Any]) -> str:
    """構造化主張からの固定テンプレート。自由文を理解・証明する処理ではない。"""
    v = {k: c["value"] for k, c in claims.items()}
    loc = v["municipality"]
    if v["eligibility"] == "out_of_scope":
        intro = f"ご相談の条件では、{loc}の「デジタル活用支援補助金」の対象条件を満たさない項目があります。"
    elif v["eligibility"] == "needs_review":
        intro = f"{loc}の「デジタル活用支援補助金」を案内するには、未確認の相談条件を補う必要があります。"
    else:
        intro = f"{loc}の「デジタル活用支援補助金」の対象候補です。"
    amounts = f"補助率は{value_label('rate', v['rate'])}、上限は{value_label('max_yen', v['max_yen'])}です。申請期限は{date_jp(v['deadline'])}です。"
    labels = {"establishment": "自治体内の事業所", "employees": "常用従業員20人以下",
              "tax": "市税の滞納がないこと", "duplicate": "同じ経費での重複補助がないこと"}
    arr = v["conditions"]
    conditions = "、".join(labels[k] for k in arr if k in labels)
    last = ("この条件なら補助金の受給・採択が確定します。" if v["award_guarantee"] else
            "これは制度案内であり、受給・採択の決定ではありません。正式な申請・審査と、職員による回答確認が必要です。" if "human_decision" in arr else "")
    return "\n\n".join(x for x in (intro, amounts, f"確認条件：{conditions}。" if conditions else "", last) if x)


def apply_changes(value: dict[str, Any], changes: dict[str, Any]) -> dict[str, Any]:
    """既存の入力項目だけを置換。コード実行・外部参照・任意ファイル参照はしない。"""
    require(type(changes) is dict, "changesはオブジェクトで指定してください。")
    paths = list(changes)
    require(all(type(p) is str and p for p in paths), "変更パスが不正です。")
    require(not any(a != b and b.startswith(a + ".") for a in paths for b in paths), "親項目と子項目の重複した変更は指定できません。")
    result = copy.deepcopy(value)
    for path, new_value in changes.items():
        current: Any = result
        parts = path.split(".")
        for i, part in enumerate(parts):
            if type(current) is list:
                require(part.isascii() and part.isdigit() and int(part) < len(current), f"存在しない配列パスです：{path}")
                key: Any = int(part)
            else:
                require(type(current) is dict and part in current, f"存在しない変更パスです：{path}")
                key = part
            if i == len(parts) - 1:
                current[key] = copy.deepcopy(new_value)
            else:
                current = current[key]
    return result


class Engine:
    """業務要求パケットを信頼基準に、要求→主張→資料→判定を対応付ける。"""

    def __init__(self, data: dict[str, Any]):
        validate_json_tree(data)
        require(type(data) is dict and data.get("schema") == "civic-poc-cases/1.0", "cases.jsonのスキーマが不正です。")
        check_keys(data, {"schema", "metadata", "requirements", "source_catalog", "claim_metadata",
                          "base_input", "scenarios", "tests", "completions"}, "cases.json")
        anchor = {k: data[k] for k in ("requirements", "source_catalog", "claim_metadata")}
        require(digest(anchor) == REFERENCE_SHA256, "採用対象の要求・資料・主張定義が固定参照値と一致しません。入力だけの変更とは区別して、仕様をレビューしてください。")
        self.data = copy.deepcopy(data)
        self.policy = self.data["requirements"]
        self.catalog = {s["id"]: s for s in self.data["source_catalog"]}
        self.meta = self.data["claim_metadata"]
        self.policy_hash = digest(self.policy)
        self.catalog_hashes = {key: digest(s) for key, s in self.catalog.items()}
        self.names = {c["id"]: c["name"] for c in self.policy["criteria"]}
        for group in ("scenarios", "tests"):
            entries = self.data[group]
            require(type(entries) is list and 0 < len(entries) <= 200, f"{group}の件数が不正です。")
            seen: set[str] = set()
            for entry in entries:
                check_keys(entry, {"key", "label", "expected", "changes"}, group)
                string(entry["key"], group + ".key", 80)
                require(entry["key"] not in seen and entry["expected"] in STATUSES, f"{group}のキー重複または期待値不正です。")
                seen.add(entry["key"])
                string(entry["label"], group + ".label")
        self.base()  # 起動時に基準入力も検査する。

    def validate_input(self, x: Any) -> None:
        validate_json_tree(x)
        check_keys(x, {"id", "label", "as_of", "target", "applicant", "source_ids", "sources", "data_policy", "workflow", "candidate", "note", "question", "resolution_log"}, "evaluation_input")
        for key in ("id", "label", "note", "question"):
            string(x[key], key, 20000)
        iso_date(x["as_of"], "as_of")
        check_keys(x["target"], {"municipality", "program_id"}, "target")
        for key, value in x["target"].items():
            string(value, "target." + key)
        a = x["applicant"]
        check_keys(a, {"id", "label", "synthetic", "establishment", "employees", "tax_arrears", "duplicate"}, "applicant")
        string(a["id"], "applicant.id")
        string(a["label"], "applicant.label")
        require(type(a["synthetic"]) is bool, "applicant.syntheticは真偽値にしてください。")
        require(a["employees"] is None or (type(a["employees"]) is int and a["employees"] >= 0), "従業員数は0以上の整数またはnullにしてください。")
        for key in ("establishment", "tax_arrears", "duplicate"):
            require(a[key] is None or type(a[key]) is bool, f"applicant.{key}は真偽値またはnullにしてください。")
        for key in ("sources", "source_ids"):
            require(type(x[key]) is list and len(x[key]) <= 10, f"{key}は10件以下の配列にしてください。")
        for key in x["source_ids"]:
            string(key, "source_idsの要素")
        require(len(x["source_ids"]) == len(set(x["source_ids"])), "参照資料IDが重複しています。")
        source_ids: set[str] = set()
        for s in x["sources"]:
            check_keys(s, {"id", "title", "version", "year", "municipality", "program_id", "published_at", "valid_from", "valid_to", "classification", "facts", "sections", "text"}, "sourcesの要素")
            for key in ("id", "title", "version", "municipality", "program_id", "classification", "text"):
                string(s[key], "source." + key, 20000)
            require(s["id"] not in source_ids, "資料スナップショットのIDが重複しています。")
            source_ids.add(s["id"])
            require(type(s["year"]) is int and 1 <= s["year"] <= 9999, "資料の年度が不正です。")
            for key in ("published_at", "valid_from", "valid_to"):
                iso_date(s[key], "source." + key)
            require(s["valid_from"] <= s["valid_to"], "資料の有効期間が逆転しています。")
            require(type(s["facts"]) is dict and type(s["sections"]) is dict, "資料のfacts・sectionsはオブジェクトにしてください。")
            # 欠落／誤型の資料を期待値として計算に流さない。内容の変更はR08で検出。
            if s["id"] in self.catalog:
                ref = self.catalog[s["id"]]
                require(set(s["facts"]) == set(ref["facts"]), "資料の構造化項目が欠落または過剰です。")
                for key, ref_value in ref["facts"].items():
                    val = s["facts"][key]
                    if type(ref_value) in (float, int) and type(ref_value) is not bool:
                        require(type(val) in (int, float), f"資料項目{key}の数値型が不正です。")
                    else:
                        require(type(val) is type(ref_value), f"資料項目{key}の型が不正です。")
                if "deadline" in s["facts"]:
                    iso_date(s["facts"]["deadline"], "facts.deadline")
            for key, value in s["sections"].items():
                string(value, "sections." + key)
        check_keys(x["data_policy"], {"classification", "template_only", "network"}, "data_policy")
        string(x["data_policy"]["classification"], "data_policy.classification")
        string(x["data_policy"]["network"], "data_policy.network")
        require(type(x["data_policy"]["template_only"]) is bool, "template_onlyの型が不正です。")
        check_keys(x["workflow"], {"use", "human_confirmation", "external_send", "automatic_award"}, "workflow")
        string(x["workflow"]["use"], "workflow.use")
        for key in ("human_confirmation", "external_send", "automatic_award"):
            require(type(x["workflow"][key]) is bool, f"workflow.{key}の型が不正です。")
        check_keys(x["candidate"], {"program_id", "claims", "text"}, "candidate")
        string(x["candidate"]["program_id"], "candidate.program_id")
        string(x["candidate"]["text"], "candidate.text", 20000)
        claims = x["candidate"]["claims"]
        check_keys(claims, set(self.meta), "claims")
        for key, claim in claims.items():
            check_keys(claim, {"value", "source_id", "section", "source_hash"}, "claim." + key)
            string(claim["source_id"], key + ".source_id", nullable=True)
            string(claim["section"], key + ".section", nullable=True)
            require(claim["source_hash"] is None or (type(claim["source_hash"]) is str and re.fullmatch("[0-9a-f]{64}", claim["source_hash"]) is not None), f"{key}の参照ハッシュが不正です。")
        values = {k: v["value"] for k, v in claims.items()}
        string(values["municipality"], "claims.municipality")
        require(type(values["max_yen"]) is int and values["max_yen"] >= 0, "上限金額は0以上の整数にしてください。")
        require(type(values["rate"]) in (int, float) and 0 <= values["rate"] <= 1, "補助率は0～1の数値にしてください。")
        iso_date(values["deadline"], "claims.deadline")
        require(type(values["eligibility"]) is str and values["eligibility"] in {"candidate", "out_of_scope", "needs_review"}, "対象候補区分が不正です。")
        require(type(values["award_guarantee"]) is bool, "award_guaranteeは真偽値にしてください。")
        conditions = values["conditions"]
        require(type(conditions) is list and len(conditions) <= 20 and all(type(v) is str for v in conditions), "必須条件は文字列配列にしてください。")
        require(len(conditions) == len(set(conditions)), "必須条件の識別子が重複しています。")
        require(type(x["resolution_log"]) is list and len(x["resolution_log"]) <= 100, "補完履歴の形式が不正です。")
        for entry in x["resolution_log"]:
            require(type(entry) is dict and type(entry.get("prior_packet_id")) is str and re.fullmatch("RIP-DEMO-[0-9A-F]{12}", entry["prior_packet_id"]) is not None, "補完履歴に正しい前件パケットIDが必要です。")
            require(entry.get("prior_decision") == "HOLD" and type(entry.get("change")) is dict, "補完履歴の変更情報が不正です。")
            string(entry.get("source"), "resolution_log.source")

    def base(self) -> dict[str, Any]:
        x = copy.deepcopy(self.data["base_input"])
        x["sources"] = copy.deepcopy(self.data["source_catalog"])
        # build_textに渡す前に、候補値の形を検査する。
        x["candidate"]["text"] = "テンプレート生成前"
        self.validate_input(x)
        x["candidate"]["text"] = build_text(x["candidate"]["claims"])
        return x

    def input_from(self, entry: dict[str, Any]) -> dict[str, Any]:
        x = apply_changes(self.base(), entry["changes"])
        self.validate_input(x)
        if "candidate.text" not in entry["changes"] and "candidate" not in entry["changes"]:
            x["candidate"]["text"] = build_text(x["candidate"]["claims"])
        return x

    def scenario(self, key: str) -> dict[str, Any]:
        for item in self.data["scenarios"]:
            if key in (item["key"], item["changes"].get("id", self.data["base_input"]["id"])):
                return item
        raise InputError("ケース名が見つかりません：" + key)

    def eligibility(self, app: dict[str, Any]) -> str:
        limit = self.catalog["SRC-01"]["facts"]["employee_limit"]
        if (app["establishment"] is False or (type(app["employees"]) is int and app["employees"] > limit)
                or app["tax_arrears"] is True or app["duplicate"] is True):
            return "out_of_scope"
        if any(app[k] is None for k in ("establishment", "employees", "tax_arrears", "duplicate")):
            return "needs_review"
        return "candidate"

    def evaluate(self, x: dict[str, Any]) -> dict[str, Any]:
        self.validate_input(x)
        c, checks, trace = x["candidate"]["claims"], [], []
        sources = {s["id"]: s for s in x["sources"]}
        source_hashes = {key: digest(s) for key, s in sources.items()}
        for key, meta in self.meta.items():
            cl = c[key]
            status, detail = "PASS", ""
            source = sources.get(cl["source_id"])
            if not cl["source_id"] or not cl["section"]:
                status, detail = "HOLD", "この主張と資料の該当項目との対応が未登録です。"
            elif cl["source_id"] not in x["source_ids"] or source is None:
                status, detail = "HOLD", "参照する資料のスナップショットが不足しています。"
            elif cl["source_id"] != meta["source"] or cl["section"] != meta["section"] or not source["sections"].get(cl["section"]):
                status, detail = "REJECT", "主張に指定された資料・参照箇所が検査対象と一致しません。"
            else:
                expected = self.eligibility(x["applicant"]) if key == "eligibility" else source["facts"]["mandatory_conditions"] if key == "conditions" else source["facts"][key]
                matches = (isinstance(expected, list) and all(v in cl["value"] for v in expected) and all(v in expected for v in cl["value"])) if key == "conditions" else same(cl["value"], expected)
                if not matches:
                    status = "REJECT"
                    detail = f"資料・条件の値「{value_label(key, expected)}」と回答の値「{value_label(key, cl['value'])}」が一致しません。"
                elif key == "eligibility" and expected == "needs_review":
                    status, detail = "HOLD", "必要な相談者条件が未確認です。資料だけでは対象候補と確認できません。"
                elif key == "eligibility":
                    detail = "入力上の対象外条件と、対象外という案内が一致しています。受給審査ではありません。" if expected == "out_of_scope" else "合成入力の条件と募集要領の対象条件が対応しています。受給資格は確定しません。"
                elif key == "conditions":
                    detail = "案内に必要な5条件が構造化主張に含まれます。"
                elif key == "award_guarantee":
                    detail = "受給・採択を断定せず、正式な申請・審査を要する旨と一致します。"
                else:
                    detail = f"参照項目の値「{value_label(key, expected)}」と、構造化された回答の値が一致します。"
            trace.append({"key": key, "label": meta["label"], "value": cl["value"], "source_id": cl["source_id"], "section": cl["section"], "status": status, "detail": detail})

        def add(key: str, status: str, detail: str) -> None:
            checks.append({"id": key, "name": self.names[key], "status": status, "detail": detail})

        target_ok = (same(x["target"], self.policy["target"]) and x["candidate"]["program_id"] == x["target"]["program_id"] and c["municipality"]["value"] == x["target"]["municipality"])
        bad_sources = any(s["id"] in x["source_ids"] and (s["municipality"] != x["target"]["municipality"] or s["program_id"] != x["target"]["program_id"]) for s in x["sources"])
        target_ok = target_ok and not bad_sources
        add("R01", "PASS" if target_ok else "REJECT", "自治体X・指定制度と、回答および参照資料の対象が一致。" if target_ok else "依頼された自治体・制度と、回答または参照資料の対象が不一致。")
        current = []
        for key in x["source_ids"]:
            s, ref = sources.get(key), self.catalog.get(key)
            if s is None:
                current.append("HOLD")
            else:
                current.append("REJECT" if ref is None or s["version"] != ref["version"] or s["year"] != ref["year"] or x["as_of"] < s["valid_from"] or x["as_of"] > s["valid_to"] else "PASS")
        if "SRC-01" not in x["source_ids"]:
            current.append("HOLD")
        freshness = worst(current)
        add("R02", freshness, f"基準日 {x['as_of'].replace('-', '/')} は募集期間内。採用対象の資料版と一致。" if freshness == "PASS" else "対象資料が足りないため、版・募集期間を確認できません。" if freshness == "HOLD" else "基準日時点で募集期間外、または採用対象の資料版・年度と不一致。")
        missing = {"establishment": "事業所", "employees": "従業員数", "tax_arrears": "市税滞納", "duplicate": "重複補助"}
        missing_names = [label for key, label in missing.items() if x["applicant"][key] is None]
        eligible = self.eligibility(x["applicant"])
        condition_status = "HOLD" if missing_names else "PASS" if eligible == c["eligibility"]["value"] else "REJECT"
        add("R03", condition_status, "・".join(missing_names) + "が未確認。相談者条件を補うまで採用を保留。" if condition_status == "HOLD" else "相談条件から導かれる対象区分と、回答中の案内が不一致。" if condition_status == "REJECT" else "対象外となる入力条件を、回答でも対象外として案内。" if eligible == "out_of_scope" else "事業所・従業員数・滞納・重複補助の合成条件と案内が一致。")
        trace_status = worst([t["status"] for t in trace])
        details = "／".join(t["label"] + ("：根拠または入力不足" if t["status"] == "HOLD" else "：根拠と不一致") for t in trace if t["status"] != "PASS")
        add("R04", trace_status, "7つの構造化主張を、資料の該当項目と対応付けて照合。" if trace_status == "PASS" else details)
        mandatory_ok = all(k in c["conditions"]["value"] for k in self.policy["mandatory_conditions"]) and c["award_guarantee"]["value"] is False
        add("R05", "PASS" if mandatory_ok else "REJECT", "必須条件を明記。受給・採択は正式な審査による旨を表示。" if mandatory_ok else "必須条件が欠落、または受給・採択を確定したように表現。")
        dp = x["data_policy"]
        data_ok = x["applicant"]["synthetic"] is True and dp["classification"] == self.policy["allowed_data"] and dp["template_only"] is True and dp["network"] == "none" and all(s["classification"] == "public_sample" for s in x["sources"])
        add("R06", "PASS" if data_ok else "REJECT", "同梱の架空資料・合成入力と、外部通信なしの設定を確認。" if data_ok else "データ区分または処理設定が「公開サンプル＋合成入力」の範囲外。")
        w = x["workflow"]
        gate_ok = w["use"] == self.policy["permitted_use"] and w["human_confirmation"] is True and w["external_send"] is False and w["automatic_award"] is False
        add("R07", "PASS" if gate_ok else "REJECT", "職員の回答案確認に限定。対外自動送信・受給自動決定を許可しない。" if gate_ok else "職員確認の欠落、対外自動送信、または受給自動決定の設定が存在。")
        bindings = []
        for key in x["source_ids"]:
            bindings.append("HOLD" if key not in sources else "PASS" if self.catalog_hashes.get(key) == source_hashes[key] else "REJECT")
        for cl in c.values():
            bindings.append("HOLD" if not cl["source_id"] or not cl["source_hash"] or cl["source_id"] not in source_hashes else "PASS" if cl["source_hash"] == source_hashes[cl["source_id"]] else "REJECT")
        if x["candidate"]["text"] != build_text(c):
            bindings.append("REJECT")
        integrity = worst(bindings)
        add("R08", integrity, "資料の内容識別値・主張の参照・テンプレート表示文が一致。" if integrity == "PASS" else "資料や参照識別値が足りず、結合した証拠の同一性を確認できません。" if integrity == "HOLD" else "採用対象資料の内容、主張の参照識別値、または表示文に不一致。")
        return {"decision": worst([c["status"] for c in checks]), "checks": checks, "trace": trace, "source_hashes": source_hashes}

    @staticmethod
    def verification(result: dict[str, Any]) -> dict[str, Any]:
        return {"decision": result["decision"], "permitted_action": "staff_review_of_answer_draft" if result["decision"] == "PASS" else "none", "checks": result["checks"], "claim_evidence": result["trace"], "source_sha256": result["source_hashes"]}

    @staticmethod
    def unresolved(result: dict[str, Any]) -> list[dict[str, Any]]:
        return [{"requirement": c["id"], "status": c["status"], "reason": c["detail"]} for c in result["checks"] if c["status"] != "PASS"]

    def packet(self, x: dict[str, Any]) -> dict[str, Any]:
        result = self.evaluate(x)  # 呼出元の申告した判定は使わず、必ず入力から計算する。
        payload = {
            "schema": PACKET_SCHEMA, "demo_only": True, "case_id": x["id"],
            "local_execution_time": datetime.now(timezone.utc).isoformat(timespec="milliseconds").replace("+00:00", "Z"), "time_attestation": "none",
            "requirements": {"id": self.policy["id"], "version": self.policy["version"], "sha256": self.policy_hash, "specification": copy.deepcopy(self.policy)},
            "evaluation_input": copy.deepcopy(x), "verification": self.verification(result), "unresolved": self.unresolved(result),
            "scope": copy.deepcopy(SCOPE), "nonclaims": list(NONCLAIMS),
        }
        return seal(payload)

    def verify(self, packet: Any) -> dict[str, Any]:
        """採用判定と再検証成否を区別。HOLD/REJECTも正しい記録なら再現成立。"""
        validate_json_tree(packet)
        check_keys(packet, {"packet_id", "payload", "integrity"}, "packet")
        p, i = packet["payload"], packet["integrity"]
        check_keys(p, {"schema", "demo_only", "case_id", "local_execution_time", "time_attestation", "requirements", "evaluation_input", "verification", "unresolved", "scope", "nonclaims"}, "payload")
        check_keys(i, {"algorithm", "canonicalization", "sha256", "issuer_signature"}, "integrity")
        require(p["schema"] == PACKET_SCHEMA and p["demo_only"] is True, "対応するデモ用パケットではありません。")
        self.validate_input(p["evaluation_input"])
        result = self.evaluate(p["evaluation_input"])
        calculated = digest(p)
        intact = i["sha256"] == calculated and packet["packet_id"] == "RIP-DEMO-" + calculated[:12].upper()
        req = p["requirements"]
        expected_req = {"id": self.policy["id"], "version": self.policy["version"], "sha256": self.policy_hash, "specification": self.policy}
        policy_match = same(req, expected_req)
        outcome_match = same(p["verification"], self.verification(result))
        try:
            timestamp = p["local_execution_time"]
            time_ok = type(timestamp) is str and re.fullmatch(r"[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}\.[0-9]{3}Z", timestamp) is not None
            if time_ok:
                datetime.fromisoformat(timestamp.replace("Z", "+00:00"))
        except (ValueError, TypeError):
            time_ok = False
        metadata_match = (p["case_id"] == p["evaluation_input"]["id"] and p["time_attestation"] == "none" and time_ok
                          and same(p["unresolved"], self.unresolved(result)) and same(p["scope"], SCOPE) and same(p["nonclaims"], NONCLAIMS)
                          and i["algorithm"] == "SHA-256" and i["canonicalization"] == CANONICALIZATION and i["issuer_signature"] is None)
        return {"ok": intact and policy_match and outcome_match and metadata_match, "intact": intact,
                "policy_match": policy_match, "outcome_match": outcome_match, "metadata_match": metadata_match,
                "recomputed_decision": result["decision"], "history_link": "recorded_not_authenticated" if p["evaluation_input"]["resolution_log"] else "none",
                "note": "同じ参照仕様による再計算。発行者・時刻・資料の真正性の認証ではありません。"}

    def complete(self, key: str, prior: dict[str, Any]) -> dict[str, Any]:
        require(self.verify(prior)["ok"], "前件の再検証が成立していません。")
        require(prior["payload"]["verification"]["decision"] == "HOLD", "補完はHOLDの記録だけを対象とします。")
        require(key in self.data["completions"], "このケースには定義済みの合成補完がありません。")
        scenario = self.scenario(key)
        require(same(prior["payload"]["evaluation_input"], self.input_from(scenario)), "補完対象が元の代表ケースと一致しません。")
        definition = self.data["completions"][key]
        check_keys(definition, {"changes", "log"}, "completion")
        x = apply_changes(prior["payload"]["evaluation_input"], definition["changes"])
        entry = {"prior_packet_id": prior["packet_id"], **copy.deepcopy(definition["log"])}
        x["resolution_log"].append(entry)
        self.validate_input(x)
        x["candidate"]["text"] = build_text(x["candidate"]["claims"])
        return x


def seal(payload: dict[str, Any]) -> dict[str, Any]:
    """内容ハッシュの付与。電子署名ではなく、第三者が同じ関数を実行できる。"""
    payload = copy.deepcopy(payload)
    value = digest(payload)
    return {"packet_id": "RIP-DEMO-" + value[:12].upper(), "payload": payload,
            "integrity": {"algorithm": "SHA-256", "canonicalization": CANONICALIZATION, "sha256": value, "issuer_signature": None}}


def self_tests(engine: Engine) -> list[dict[str, Any]]:
    """同じファイルに回帰・不正入力・変更検出テストを同梱。実AI評価ではない。"""
    rows: list[dict[str, Any]] = []

    def check(name: str, action: Callable[[], bool]) -> None:
        try:
            ok = action() is True
            rows.append({"name": name, "passed": ok, "detail": "OK" if ok else "期待を満たしませんでした。"})
        except Exception as exc:
            rows.append({"name": name, "passed": False, "detail": f"{type(exc).__name__}: {exc}"})

    def invalid_input(changes: dict[str, Any]) -> bool:
        try:
            engine.evaluate(apply_changes(engine.base(), changes))
        except InputError:
            return True
        return False

    def invalid_json(text: str) -> bool:
        try:
            parse_json(text)
        except InputError:
            return True
        return False

    base_packet = engine.packet(engine.base())

    def blocked_packet(changes: dict[str, Any], rehash: bool = True) -> bool:
        value = apply_changes(base_packet, changes)
        if rehash:
            updated = seal(value["payload"])
            value["packet_id"] = updated["packet_id"]
            value["integrity"]["sha256"] = updated["integrity"]["sha256"]
        try:
            return engine.verify(value)["ok"] is False
        except InputError:
            return True

    for group in ("scenarios", "tests"):
        for item in engine.data[group]:
            check("期待判定 / " + item["key"], lambda t=item: engine.evaluate(engine.input_from(t))["decision"] == t["expected"])
            check("記録の再検証 / " + item["key"], lambda t=item: engine.verify(engine.packet(engine.input_from(t)))["ok"])
    for key in ("missing", "unsupported"):
        def complete_test(k: str = key) -> bool:
            before = engine.packet(engine.input_from(engine.scenario(k)))
            unchanged = canonical(before)
            after = engine.packet(engine.complete(k, before))
            return (before["payload"]["verification"]["decision"] == "HOLD" and after["payload"]["verification"]["decision"] == "PASS"
                    and canonical(before) == unchanged and engine.verify(after)["ok"]
                    and after["payload"]["evaluation_input"]["resolution_log"][-1]["prior_packet_id"] == before["packet_id"])
        check("補完・前件保持 / " + key, complete_test)
    mutations = {
        "従業員数のboolを拒否": {"applicant.employees": True},
        "負の従業員数を拒否": {"applicant.employees": -1},
        "文字列の従業員数を拒否": {"applicant.employees": "8"},
        "文字列の真偽値を拒否": {"applicant.tax_arrears": "false"},
        "存在しない日付を拒否": {"as_of": "2026-02-30"},
        "基準日nullを拒否": {"as_of": None},
        "資料ID重複を拒否": {"source_ids": ["SRC-01", "SRC-01"]},
        "資料重複を拒否": {"sources": [engine.base()["sources"][0]] * 2},
        "空の主張集合を拒否": {"candidate.claims": {}},
        "金額のboolを拒否": {"candidate.claims.max_yen.value": True},
        "補助率のboolを拒否": {"candidate.claims.rate.value": True},
        "不正な主張日付を拒否": {"candidate.claims.deadline.value": "2026-13-01"},
        "曖昧なハッシュ文字列を拒否": {"candidate.claims.max_yen.source_hash": "bad"},
        "必須条件IDの重複を拒否": {"candidate.claims.conditions.value": ["tax", "tax"]},
        "未定義の主張を拒否": {"candidate.claims": {**engine.base()["candidate"]["claims"], "unknown": {"value": True}}},
        "安全整数域外を拒否": {"applicant.employees": MAX_SAFE_INTEGER + 1},
        "受理域外の小数精度を拒否": {"candidate.claims.rate.value": 0.123},
    }
    for name, changes in mutations.items():
        check(name, lambda c=changes: invalid_input(c))
    for name, text in (("JSONキーの重複を拒否", '{"a":1,"a":2}'), ("NaNを拒否", '{"x":NaN}'),
                       ("Infinityを拒否", '{"x":Infinity}'), ("壊れたJSONを拒否", '{"x":'),
                       ("不正Unicodeを拒否", '{"x":"\\ud800"}')):
        check(name, lambda t=text: invalid_json(t))
    packet_mutations = {
        "判定改変＋ハッシュ再計算を検出": {"payload.verification.decision": "REJECT"},
        "許可操作だけの改変を検出": {"payload.verification.permitted_action": "external_send"},
        "要求IDの差替えを検出": {"payload.requirements.id": "OTHER"},
        "要求版の差替えを検出": {"payload.requirements.version": "2.0"},
        "要求本文の差替えを検出": {"payload.requirements.specification.permitted_use": "automatic_award"},
        "ケースIDの不一致を検出": {"payload.case_id": "OTHER"},
        "未確認事項の改変を検出": {"payload.unresolved": [{"requirement": "R01", "status": "HOLD", "reason": "変更"}]},
        "保証範囲の水増しを検出": {"payload.scope.real_world_validation": True},
        "対象外注記の削除を検出": {"payload.nonclaims": []},
        "時刻認証の虚偽表示を検出": {"payload.time_attestation": "certified"},
        "時刻の不正形式を検出": {"payload.local_execution_time": "2026-02-30T00:00:00.000Z"},
        "未知スキーマを拒否": {"payload.schema": "unknown"},
        "署名付きとの虚偽表示を検出": {"integrity.issuer_signature": "not-a-signature"},
        "ハッシュ方式の差替えを検出": {"integrity.algorithm": "MD5"},
        "正規化方式の差替えを検出": {"integrity.canonicalization": "OTHER"},
    }
    for name, changes in packet_mutations.items():
        check(name, lambda c=changes: blocked_packet(c))
    check("本文の変更をハッシュで検出", lambda: blocked_packet({"payload.evaluation_input.candidate.text": "変更された文"}, False))
    check("自由文と構造化主張の不一致をR08で拒否", lambda: engine.evaluate(apply_changes(engine.base(), {"candidate.text": "独自に追記された無検証の文"}))["decision"] == "REJECT")
    check("全参照の欠落ではPASSにしない", lambda: engine.evaluate(apply_changes(engine.base(), {"source_ids": []}))["decision"] == "HOLD")
    check("REJECTはHOLDより優先", lambda: engine.evaluate(apply_changes(engine.base(), {"applicant.employees": None, "workflow.external_send": True}))["decision"] == "REJECT")
    check("外部通信を許可する申告を拒否", lambda: engine.evaluate(apply_changes(engine.base(), {"data_policy.network": "enabled"}))["decision"] == "REJECT")

    def changed_source() -> bool:
        x = engine.base()
        x["sources"][0]["facts"]["max_yen"] = 600000
        x["sources"][0]["text"] = x["sources"][0]["text"].replace("上限30万円", "上限60万円")
        x["candidate"]["claims"]["max_yen"]["value"] = 600000
        for cl in x["candidate"]["claims"].values():
            if cl["source_id"] == "SRC-01":
                cl["source_hash"] = digest(x["sources"][0])
        x["candidate"]["text"] = build_text(x["candidate"]["claims"])
        r = engine.evaluate(x)
        return r["decision"] == "REJECT" and r["checks"][-1]["status"] == "REJECT"
    check("資料と参照ハッシュの同時変更も固定資料照合で拒否", changed_source)

    def changed_reference() -> bool:
        data = copy.deepcopy(engine.data)
        data["requirements"]["criteria"] = []
        try:
            Engine(data)
        except InputError:
            return True
        return False
    check("固定参照仕様の差替えを起動時に拒否", changed_reference)
    fake_expectation = copy.deepcopy(engine.scenario("normal"))
    fake_expectation["expected"] = "REJECT"
    check("期待ラベルを判定入力に使わない", lambda: engine.evaluate(engine.input_from(fake_expectation))["decision"] == "PASS")
    check("JSONの整数1と小数1.0をHTMLと同様に照合", lambda: canonical(1.0) == canonical(1))
    check("JSONの真偽値と数値を区別", lambda: not same(True, 1))
    check("Unicodeキー順序はUTF-16順", lambda: canonical({"\ue000": 1, "😀": 2}).index("😀") < canonical({"\ue000": 1, "😀": 2}).index("\ue000"))
    return rows


def create_output(root: Path, kind: str) -> Path:
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%S")
    path = root / f"{kind}-{stamp}Z-{uuid.uuid4().hex[:6]}"
    path.mkdir(parents=True, exist_ok=False)
    return path


def save_record(engine: Engine, folder: Path, x: dict[str, Any], group: str, key: str,
                label: str, expected: str, prior_id: str | None = None) -> dict[str, Any]:
    packet = engine.packet(x)
    replay = engine.verify(packet)
    decision = packet["payload"]["verification"]["decision"]
    packet_name = "packets/" + packet["packet_id"] + ".json"
    path = folder / packet_name
    if path.exists():
        require(same(read_json(path), packet), "短縮パケットIDが衝突したため保存を停止しました。")
    else:
        write_json(path, packet)
    # 実際にディスクから読み直す。計算時のオブジェクトの自己比較だけにしない。
    saved_check = engine.verify(read_json(path))
    draft_name = None
    if decision == "PASS" and replay["ok"] and saved_check["ok"]:
        draft_name = "drafts/" + packet["packet_id"] + ".txt"
        (folder / draft_name).write_text("【架空データ／職員確認用の回答案】\n受給・採択の決定や、住民への自動送信には使用しません。\n\n" + x["candidate"]["text"] + "\n", encoding="utf-8")
    return {"group": group, "key": key, "label": label, "case_id": x["id"], "expected": expected,
            "actual": decision, "matched": decision == expected, "packet_id": packet["packet_id"],
            "packet_file": packet_name, "draft_file": draft_name, "prior_packet_id": prior_id,
            "reverification": saved_check, "checks": packet["payload"]["verification"]["checks"],
            "claim_evidence": packet["payload"]["verification"]["claim_evidence"],
            "unresolved": packet["payload"]["unresolved"], "_packet": packet}


def report_html(summary: dict[str, Any], records: list[dict[str, Any]], tests: list[dict[str, Any]]) -> str:
    esc = lambda v: html.escape(str(v), quote=True)

    def badge(status: str) -> str:
        return f'<span class="badge {esc(status.lower())}">{esc(status)}</span>'

    def row(record: dict[str, Any], detailed: bool = False) -> str:
        issues = record["unresolved"]
        explanation = "指定8条件を通過。職員が確認する回答案として扱えます。" if not issues else " / ".join(c["requirement"] + "：" + c["reason"] for c in issues)
        links = f'<a href="{esc(record["packet_file"])}">責任情報パケット JSON</a>'
        if record["draft_file"]:
            links += f' · <a href="{esc(record["draft_file"])}">職員確認用の回答案</a>'
        else:
            links += ' · <span class="muted">採用用ファイルは出力しません</span>'
        details = ""
        if detailed:
            checks = "".join(f'<tr><td>{esc(c["id"])}</td><td>{esc(c["name"])}</td><td>{badge(c["status"])}</td><td>{esc(c["detail"])}</td></tr>' for c in record["checks"])
            claims = "".join(f'<tr><td>{esc(c["label"])}</td><td>{esc(c["source_id"] or "未登録")} / {esc(c["section"] or "未登録")}</td><td>{badge(c["status"])}</td><td>{esc(c["detail"])}</td></tr>' for c in record["claim_evidence"])
            details = f'<details><summary>8条件と7主張の確認内容を見る</summary><div class="scroll"><table>{checks}</table><h4>主張と根拠の対応</h4><table>{claims}</table></div></details>'
        return f'<article class="case"><div class="case-title"><div><small>{esc(record["case_id"])}</small><h3>{esc(record["label"])}</h3></div>{badge(record["actual"])}</div><p>{esc(explanation)}</p><div class="links">{links}</div>{details}</article>'

    main = "".join(row(r, True) for r in records if r["group"] == "scenario")
    complete = "".join(row(r, True) + f'<p class="history">補完前のHOLD記録：<a href="packets/{esc(r["prior_packet_id"])}.json">{esc(r["prior_packet_id"])}</a> → 上記の新しい記録。前件は上書きしていません。</p>' for r in records if r["group"] == "completion")
    reference_rows = "".join(f'<tr><td>{esc(r["case_id"])}</td><td>{esc(r["label"])}</td><td>{badge(r["expected"])}</td><td>{badge(r["actual"])}</td><td>{"一致" if r["matched"] else "不一致"}</td><td><a href="{esc(r["packet_file"])}">JSON</a></td></tr>' for r in records if r["group"] == "reference_test")
    test_rows = "".join(f'<tr><td>{esc(t["name"])}</td><td>{"OK" if t["passed"] else "失敗"}</td><td>{esc(t["detail"])}</td></tr>' for t in tests)
    references = summary["reference_tests"]
    replay = summary["reverification"]
    status = "実行・照合が完了しました" if summary["ok"] else "不一致またはテスト失敗があります"
    return '''<!doctype html><html lang="ja"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; style-src 'unsafe-inline'; img-src data:; base-uri 'none'; form-action 'none'">
<title>第1弾PoC｜Python実行結果</title><style>
*{box-sizing:border-box}body{margin:0;background:#f3f6f7;color:#153442;font:14px/1.85 -apple-system,BlinkMacSystemFont,"Yu Gothic UI",Meiryo,sans-serif}main{max-width:1120px;margin:auto;padding:36px 28px 65px}header{background:#102d3b;color:white;padding:18px 28px}.head{max-width:1064px;margin:auto;display:flex;justify-content:space-between;gap:16px;font-size:12px}h1{font-size:32px;line-height:1.5;margin:8px 0 12px}h2{font-size:22px;margin:32px 0 12px}h3{font-size:17px;margin:0}h4{margin:18px 0 8px}p{margin:9px 0}.kicker{font-size:11px;letter-spacing:.14em;color:#087c70;font-weight:750}.intro{max-width:800px;color:#536d78}.notice{border-left:3px solid #087c70;background:#e8f4ef;padding:13px 17px;margin:20px 0}.metrics{display:grid;grid-template-columns:repeat(3,1fr);gap:14px}.metric,.case{background:white;border:1px solid #dbe5e9;border-radius:12px;padding:18px 20px}.metric b{display:block;font-size:29px;line-height:1.6}.metric span,.muted{color:#637b87;font-size:12px}.case{margin:12px 0}.case-title{display:flex;justify-content:space-between;align-items:center;gap:16px}small{color:#708793;font-family:monospace}.case p{font-size:12px}.badge{display:inline-block;border-radius:6px;padding:3px 9px;font:700 11px/1.7 monospace;white-space:nowrap}.pass{background:#e6f4ed;color:#086d5d}.hold{background:#fff3d9;color:#8e5b06}.reject{background:#fbe9e9;color:#a82f38}.links{font-size:12px;margin:11px 0}a{color:#087467;text-underline-offset:3px}.flow{display:flex;justify-content:space-between;gap:20px;margin:23px 0;padding:14px 0;border-top:1px solid #d6e2e7;border-bottom:1px solid #d6e2e7;font-weight:700}.flow small{display:block;font-family:inherit}details{margin-top:12px;border-top:1px solid #e4ebee;padding-top:10px}summary{cursor:pointer;font-size:12px;font-weight:700}.scroll{overflow:auto}table{border-collapse:collapse;width:100%;font-size:11px;margin-top:12px}td,th{text-align:left;vertical-align:top;padding:10px;border-bottom:1px solid #e0e8eb}th{background:#eaf0f3}code{font:12px/1.8 Consolas,monospace;overflow-wrap:anywhere}pre{white-space:pre-wrap;background:#102d3b;color:#dcebe9;padding:16px 20px;border-radius:9px}.history{font-size:11px;color:#5c7682;padding:0 8px 10px;overflow-wrap:anywhere}.fine{font-size:11px;color:#617884;overflow-wrap:anywhere}footer{margin-top:28px;padding-top:15px;border-top:1px solid #dbe5e9}.steps{display:grid;grid-template-columns:1fr 1fr;gap:20px}.steps>div{background:#fff;border:1px solid #dbe5e9;padding:18px 20px;border-radius:12px}
@media(max-width:720px){main{padding:24px 16px}h1{font-size:25px}.metrics{grid-template-columns:1fr}.metric b{font-size:25px}.flow{font-size:11px;gap:8px}.flow small{font-size:10px}.steps{grid-template-columns:1fr}.head{font-size:10px}.case-title{align-items:start}.case{padding:15px}h3{font-size:15px}td{min-width:60px}table{min-width:620px}}
</style></head><body><header><div class="head"><b>自治体AI 回答採用アシュアランス</b><span>Python PoC 1.0 · 合成データのみ</span></div></header><main>''' + f'''
<div class="kicker">PHASE 01 / EXECUTION REPORT</div><h1>何が進み、何が止まったか。</h1>
<p class="intro">{esc(status)}。このページはPythonが実際に生成した結果です。元の操作デモHTMLは変更していません。まず代表6ケースの判定と理由を確認してください。</p>
<div class="notice"><strong>PASS＝職員が確認する回答案として採用可。</strong> 補助金の受給・採択決定ではありません。制度・自治体・資料・相談者はすべて架空です。</div>
<div class="flow"><div>① 業務要求パケット<small>採用対象の8条件・版を固定</small></div><div>→</div><div>② 回答案の採用判定<small>PASS / HOLD / REJECT</small></div><div>→</div><div>③ 責任情報パケット<small>根拠・未確認事項・再検証</small></div></div>
<div class="metrics"><div class="metric"><span>参考ケースの期待判定との一致</span><b>{references['matched']} / {references['total']}</b><span>ルール試験。実AIの正答率ではありません。</span></div><div class="metric"><span>保存パケットの再検証成立</span><b>{replay['passed']} / {replay['total']}</b><span>HOLD・REJECTの記録も含みます。</span></div><div class="metric"><span>異常入力を含む自己テスト</span><b>{summary['self_tests']['passed']} / {summary['self_tests']['total']}</b><span>既知のケースに対する実装確認です。</span></div></div>
<h2>01　まず代表ケースを見る</h2><p class="muted">上限額が合っていても、根拠への対応がなければHOLD。不整合があればREJECTです。</p>{main or '<p>この実行では代表ケースを選択していません。</p>'}
<h2>02　不足を補い、もう一度判定する</h2><p class="muted">合成の属性値や根拠参照を補完した例です。実住民への確認ではありません。ログは前件IDを記録しますが、確認者の認証や履歴の完全性を保証しません。</p>{complete or '<p>この実行には補完ケースを含めていません。</p>'}
<h2>03　参考テストの内訳</h2><p>PASS {references['counts']['PASS']}件 / HOLD {references['counts']['HOLD']}件 / REJECT {references['counts']['REJECT']}件。</p>
<details><summary>全{references['total']}件の期待値・実際の判定を見る</summary><div class="scroll"><table><thead><tr><th>ID</th><th>ケース</th><th>期待</th><th>実際</th><th>照合</th><th>記録</th></tr></thead><tbody>{reference_rows}</tbody></table></div></details>
<details><summary>自己テスト{summary['self_tests']['total']}件の結果を見る</summary><div class="scroll"><table>{test_rows}</table></div></details>
<h2>04　保存した結果を再検証する</h2><div class="steps"><div><h3>Pythonで再検証</h3><p>プロジェクトのフォルダで、次を実行します。</p><pre><code>python poc.py verify output</code></pre><p class="fine">このコマンドは全実行フォルダ内の責任情報パケットを再検証します。再検証成立と採用可は別です。</p></div><div><h3>元HTMLで再検証</h3><p>元HTMLの「要求と証拠」→「JSONを読み込む」で、各ケースのJSONを選択します。</p><p class="fine">元HTMLは読み込んだ記録の検証結果を表示します。上部の選択ケースやデモ画面自体をPythonの結果に切り替える機能ではありません。</p></div></div>
<h2>検証範囲と公表時の注意</h2><p>実装したのは、構造化された要求・主張・根拠参照の照合、理由付き判定、保存記録の再計算です。<strong>生成AIの呼出し、自由文の完全な意味検証、形式証明、実住民の属性確認、資料発行者の認証、法令への包括適合、実運用のプライバシー保証は実装していません。</strong></p>
<p>ハッシュは内容の照合用で、電子署名や時刻認証ではありません。元HTML・本Python・参照データの正当な版を信頼して使う必要があります。期待判定との一致をAI精度・事故防止率として公表しないでください。社名・公表文・実装コードの開示範囲は両社で別途確認してください。</p>
<footer class="fine">実行時刻（ローカルPC時計のUTC表記・時刻認証なし）：{esc(summary['executed_at_utc'])}<br>固定基準日：2026-10-01（境界値テストを除く） / Python {esc(summary['python_version'])}<br>poc.py SHA-256：{esc(summary['python_sha256'])}<br>cases.json SHA-256：{esc(summary['data_sha256'])}<br>元HTML：{esc(summary['original_html_status'])}<br><a href="summary.json">機械可読の結果サマリー</a> · <a href="self_test_report.json">自己テスト記録</a></footer>
</main></body></html>'''


def run(engine: Engine, data_path: Path, out_root: Path, selected: str | None = None,
        completion_only: str | None = None) -> tuple[Path, bool]:
    # ケースの解決に失敗しただけで、空の実行フォルダを残さない。
    selected_items = [engine.scenario(completion_only or selected)] if (completion_only or selected) else engine.data["scenarios"]
    folder = create_output(out_root, "run")
    (folder / "packets").mkdir()
    (folder / "drafts").mkdir()
    records: list[dict[str, Any]] = []
    prior_packets = {}
    for item in selected_items:
        r = save_record(engine, folder, engine.input_from(item), "scenario", item["key"], item["label"], item["expected"])
        records.append(r)
        prior_packets[item["key"]] = r["_packet"]
    if not selected and not completion_only:
        for item in engine.data["tests"]:
            records.append(save_record(engine, folder, engine.input_from(item), "reference_test", item["key"], item["label"], item["expected"]))
    completion_keys = [completion_only] if completion_only else ["missing", "unsupported"] if not selected else []
    for key in completion_keys:
        require(key is not None and key in prior_packets, "補完元のパケットがありません。")
        prior = prior_packets[key]
        x = engine.complete(key, prior)
        records.append(save_record(engine, folder, x, "completion", key + "_completed", engine.scenario(key)["label"] + " → 補完後", "PASS", prior["packet_id"]))
    tests = self_tests(engine)
    successful_tests = sum(t["passed"] for t in tests)
    reference = [r for r in records if r["group"] == "reference_test"]
    counts = Counter(r["actual"] for r in reference)
    py_path = Path(__file__).resolve()
    original_html = ROOT / "civic_ai_poc_demo.html"
    original_status = "未同梱（Python実行には不要）"
    if original_html.is_file():
        actual = hashlib.sha256(original_html.read_bytes()).hexdigest()
        original_status = "元ファイルとSHA-256一致・未変更" if actual == ORIGINAL_HTML_SHA256 else "元ファイルと不一致。HTML互換性の前提を再確認してください。"
    ok = all(r["matched"] and r["reverification"]["ok"] for r in records) and successful_tests == len(tests)
    summary = {
        "schema": "civic-poc-run-report/1.0", "demo_only": True, "ok": ok,
        "executed_at_utc": datetime.now(timezone.utc).isoformat(timespec="milliseconds").replace("+00:00", "Z"),
        "python_version": sys.version.split()[0], "engine_version": VERSION,
        "python_sha256": hashlib.sha256(py_path.read_bytes()).hexdigest(), "data_sha256": hashlib.sha256(data_path.read_bytes()).hexdigest(),
        "reference_sha256": REFERENCE_SHA256, "original_html_status": original_status,
        "reference_tests": {"total": len(reference), "matched": sum(r["matched"] for r in reference), "counts": {s: counts[s] for s in STATUSES}},
        "reverification": {"total": len(records), "passed": sum(r["reverification"]["ok"] for r in records)},
        "self_tests": {"total": len(tests), "passed": successful_tests},
        "records": [{k: v for k, v in r.items() if k != "_packet"} for r in records],
        "limitations": ["Synthetic rule tests, not AI accuracy", "No live AI or real municipality integration", "No legal/privacy certification", "No issuer authentication or trusted timestamp", "History references are recorded, not authenticated"],
    }
    write_json(folder / "summary.json", summary)
    write_json(folder / "self_test_report.json", {"schema": "civic-poc-self-tests/1.0", "total": len(tests), "passed": successful_tests, "results": tests})
    (folder / "report.html").write_text(report_html(summary, records, tests), encoding="utf-8")
    print("\n自治体AI・回答採用アシュアランス / 第1弾PoC\n")
    for r in records:
        if r["group"] != "reference_test":
            print(f"  {r['actual']:6}  {r['label']}")
    if reference:
        print(f"\n参考テスト：{sum(r['matched'] for r in reference)}/{len(reference)}件一致（PASS {counts['PASS']} / HOLD {counts['HOLD']} / REJECT {counts['REJECT']}）")
    print(f"保存記録の再検証：{sum(r['reverification']['ok'] for r in records)}/{len(records)}件成立")
    print(f"自己テスト：{successful_tests}/{len(tests)}件成功")
    print(f"\n結果を見る：{folder / 'report.html'}")
    print("元HTMLは変更していません。実AI・実住民情報・実行政システムへの接続はありません。")
    print("PASSは職員確認用の回答案のみ。再検証成立は受給資格や発行者の認証ではありません。")
    if not ok:
        print("\n注意：不一致があります。summary.json / self_test_report.json を確認してください。", file=sys.stderr)
    return folder, ok


def verify_path(engine: Engine, target: Path) -> bool:
    if target.is_dir():
        paths = sorted(p for p in target.rglob("RIP-DEMO-*.json") if p.is_file())
    else:
        paths = [target]
    require(0 < len(paths) <= 2000, "対象は1～2000件の責任情報パケットにしてください。フォルダ指定ではRIP-DEMO-*.jsonを探します。")
    good = 0
    for path in paths:
        try:
            value = engine.verify(read_json(path))
            good += int(value["ok"])
            print(f"{'成立' if value['ok'] else '不成立'} / 再計算={value['recomputed_decision']} / {path.name}")
            if not value["ok"]:
                print(json.dumps(value, ensure_ascii=False))
        except (InputError, OSError, UnicodeError, KeyError, TypeError, RecursionError) as exc:
            print(f"不成立 / {path.name} / {exc}", file=sys.stderr)
    print(f"\n再検証：{good}/{len(paths)}件成立。HOLD・REJECTをPASSに変更する処理ではありません。")
    print("履歴中の前件IDは記録内容として照合しますが、確認者の認証や履歴全体の完全性は検証しません。")
    return good == len(paths)


def cli() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--version", action="version", version=VERSION)
    parser.add_argument("--data", type=Path, default=ROOT / "cases.json", help="ダミーデータJSON（既定は本Pythonと同じフォルダ）")
    parser.add_argument("--out", type=Path, default=ROOT / "output", help="出力先。実行ごとに別フォルダを作成")
    commands = parser.add_subparsers(dest="command")
    run_parser = commands.add_parser("run", help="代表6件・参考30件・補完2件を実行")
    run_parser.add_argument("--case", help="代表ケースのキーまたはCASE-01等を1件指定")
    complete_parser = commands.add_parser("complete", help="補完前と補完後を別記録として実行")
    complete_parser.add_argument("case", choices=["missing", "unsupported"])
    verify_parser = commands.add_parser("verify", help="保存済みパケットまたはフォルダを再検証")
    verify_parser.add_argument("path", type=Path)
    commands.add_parser("test", help="回帰・異常入力・変更検出の自己テスト")
    # --data/--outはサブコマンドの前後どちらでも使える。
    for sub in (run_parser, complete_parser, verify_parser, commands.choices["test"]):
        sub.add_argument("--data", type=Path, default=argparse.SUPPRESS, help=argparse.SUPPRESS)
        sub.add_argument("--out", type=Path, default=argparse.SUPPRESS, help=argparse.SUPPRESS)
    args = parser.parse_args()
    try:
        engine = Engine(read_json(args.data))
        command = args.command or "run"
        if command == "verify":
            return 0 if verify_path(engine, args.path) else 1
        if command == "test":
            tests = self_tests(engine)
            passed = sum(t["passed"] for t in tests)
            folder = create_output(args.out, "test")
            write_json(folder / "self_test_report.json", {"schema": "civic-poc-self-tests/1.0", "total": len(tests), "passed": passed, "results": tests})
            for item in tests:
                if not item["passed"]:
                    print("失敗：" + item["name"] + " / " + item["detail"], file=sys.stderr)
            print(f"自己テスト：{passed}/{len(tests)}件成功\n結果：{folder / 'self_test_report.json'}")
            return 0 if passed == len(tests) else 1
        _, ok = run(engine, args.data, args.out, selected=getattr(args, "case", None) if command == "run" else None,
                    completion_only=args.case if command == "complete" else None)
        return 0 if ok else 1
    except (InputError, OSError, UnicodeError, KeyError, TypeError, RecursionError) as exc:
        print(f"入力・実行エラー：{exc}\nこの入力を採用可として扱わないでください。", file=sys.stderr)
        return 2


if __name__ == "__main__":
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    raise SystemExit(cli())
