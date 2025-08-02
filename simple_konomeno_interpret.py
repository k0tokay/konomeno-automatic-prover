import itertools
from collections import OrderedDict, defaultdict
from typing import Dict, List, NamedTuple, Optional, Tuple

import pegtree as pg

import predicate_logic_ast as logic
import simple_konomeno_ast as kono_ast
from simple_konomeno_ast import rec_template, rec_template_with_quantifier

_label_counter = itertools.count(100)


def max_label(ast):
    """
    ASTの全てのLTermのlabelの最大値を返す．
    """
    max_label = 0

    @rec_template
    def rec(ast):
        sub_index = ast.sub_index
        if sub_index is not None:
            nonlocal max_label
            max_label = max(max_label, sub_index)
        return rec(ast.term)

    rec(ast)
    return max_label


def add_label(ast, start_label=None):
    """
    ASTの全てのLTermにlabelをつける．
    """
    if start_label is None:
        start_label = max_label(ast) + 1

    _label_counter = itertools.count(start_label)

    @rec_template
    def rec(ast):
        match ast:
            case kono_ast.LTerm(term, is_indiv, sup_indices, sub_index):
                if sub_index is None:
                    sub_index = next(_label_counter)
                return kono_ast.LTerm(rec(term), is_indiv, sup_indices, sub_index)

    return rec(ast)


# 返値の型エイリアス
ScopeMap = Dict[Tuple[str, int | None], List[kono_ast.LTerm]]
ScopeDict = Dict[int, List[kono_ast.LTerm]]


def strip_sup(term: kono_ast.LTerm | kono_ast.AST):
    """
    LTerm の鎖 (sup_indices を外側→内側に持つ) を剥いで
    最深部 (= 添字の無い基底項) を返す。
    """
    t = term
    while isinstance(t, kono_ast.LTerm):
        t = t.term  # LTerm(term, sup_indices) の term を辿る
    return t


def group_by_subindex(lterms: List[kono_ast.LTerm]) -> ScopeDict:
    """
    Parameters
    ----------
    lterms : search_scope で束縛元が分かった LTerm 群
             （量化子 q,i が同じクラスに属するもの）
    Returns
    -------
    groups : {sub_index: [LTerm, ...]}  昇順で安定化
    """
    base2sub: "OrderedDict[int, int]" = OrderedDict()  # id(base) → sub_index
    groups: ScopeDict = {}

    for lt in lterms:
        base = strip_sup(lt)  # 添字の無い基底項
        key = id(base)

        # まだ sub_index が無ければ採番
        if key not in base2sub:
            sub_idx = len(base2sub)  # 0,1,2…  登場順
            base2sub[key] = sub_idx
        else:
            sub_idx = base2sub[key]

        groups.setdefault(sub_idx, []).append(lt)

    return groups


def search_scope(ast) -> ScopeMap:
    """
    discourse 全体を DFS して
        (量化子記号, ラベル or None)  ↦  束縛される LTerm オブジェクト群
    を返す。量化子がラベル無しなら key=(q, None)。
    """
    env_stack: list[Tuple[str, int | None]] = []  # [(q, i), …]  外→内
    bound: ScopeMap = defaultdict(list)
    seen_ids: set[int] = set()  # 再登録の重複防止

    # --------------------------------------------------------------
    @rec_template_with_quantifier
    def walk(node):
        match node:
            # ---- 量化子ノード ------------------------------------
            case kono_ast.Quantified(qop, body):
                if qop.label:
                    env_stack.append((qop.quantifier, qop.label[0]))
                else:
                    env_stack.append((qop.quantifier, None))
                walk(body)
                env_stack.pop()

            case kono_ast.PullDown(qop, body):
                if qop.label:
                    env_stack.append((qop.quantifier, qop.label[0]))
                else:
                    env_stack.append((qop.quantifier, None))
                walk(body)
                env_stack.pop()

            # ---- LTerm：sup_index と環境スタックの照合 ----------
            case kono_ast.LTerm(inner, sups):
                for sup in sups:
                    for q, lab in reversed(env_stack):
                        if sup.quantifier != q:
                            continue
                        if lab is None or sup.label == lab:
                            key = (q, lab)  # 束縛元
                            if id(node) not in seen_ids:
                                bound[key].append(node)
                                seen_ids.add(id(node))
                            break  # 最も近い束縛で確定
                walk(inner)  # 内側の項を続行

    walk(ast)
    return bound


def build_first_scope(scopes_dict: ScopeDict, rec):
    """
    scopes_dict : {sub_index: [LTerm, …]}
      └ replace_scope が返す “同値クラス毎に集めた LTerm 群”
    rec         : Interpret 内部で使っている AST→logic 変換関数

    返り値      : 第1スコープ (= 交叉 ∩ と直積 × で組んだ論理式)
    """
    # 1) サブインデックスの安定順序を決定
    key_order = sorted(scopes_dict.keys())

    # 2) クラス毎に ∩ を立てる
    class_domains: list[logic.Node] = []
    for k in key_order:
        atoms = [rec(t) for t in scopes_dict[k]]
        class_domains.append(atoms[0] if len(atoms) == 1 else logic.Cap(atoms))

    # 3) クラスが 1 つならそのまま、複数あれば ×（Prod）
    return class_domains[0] if len(class_domains) == 1 else logic.Prod(class_domains)


def replace_scope(body_ast, scope_dict: ScopeDict):
    """
    Parameters
    ----------
    body_ast    : Quantified / PullDown の body 部分 (AST)
    scope_dict  : search_scope → group_by_subindex などで得た
                  {sub_index: [LTerm, ...]} という “同値クラス” 辞書

    Returns
    -------
    new_body    : LTerm を Var に置換した AST
    var_order   : List[logic.Var]
                  sub_index の昇順で並べた “導入された変数” リスト
    """

    # ------------------------------------------------------------------
    # 1) 置換マップを作成:  id(LTerm) ↦ logic.Var
    # ------------------------------------------------------------------
    key_order: List[int] = sorted(scope_dict.keys())  # 安定した順序
    var_order: List[logic.Var] = []  # 戻り値用

    replace_map: Dict[int, logic.Var] = {}  # id(node) → Var
    for k in key_order:
        var = logic.Var(f"x{k}")
        var_order.append(var)
        for lt in scope_dict[k]:
            replace_map[id(lt)] = var

    # ------------------------------------------------------------------
    # 2) body_ast を DFS し、該当 LTerm を Var に差し替え
    #    （量化子境界は rec_template_with_quantifier が自動でスキップ）
    # ------------------------------------------------------------------
    @rec_template_with_quantifier
    def walk(node):
        # LTerm ノードだけがここに来る
        match node:
            case kono_ast.LTerm(term, sup_indices):
                rep = replace_map.get(id(node))
                if rep is not None:
                    return rep  # ← 置換成功
                # 束縛対象でなければ再帰的に内部を探索
                return kono_ast.LTerm(walk(term), sup_indices)
            case _:
                return node  # 量化子などはそのまま

    new_body = walk(body_ast)
    return new_body, var_order


def appline_list(max_length: int = 15):
    """
    result_ordered[i] には
        ・非ブランクトークンの個数 == i
        ・ブランク数が少ない順（0,1,2,...）
    で重複なし・挿入順保持の語形を並べる。
    """
    # Ordered-Set としての buckets[non_blank_len]
    buckets = [dict() for _ in range(max_length + 1)]

    def add(form: str):
        """重複を除きつつ buckets へ追加"""
        nblen = len(form) - form.count("_")  # 非ブランク長
        if 0 <= nblen <= max_length and form not in buckets[nblen]:
            buckets[nblen][form] = None
            return True
        return False

    # ---------- レイヤー 0（省略なし） ----------
    for n in range(max_length + 1):
        if n % 2 == 1:
            add("t" + "Rt" * (n // 2))  # tRtRt...
    for n in range(max_length + 1):
        if n >= 2:
            add("tR" + "t" * (n - 2))  # tRtt...

    # ---------- レイヤー 1 以降 ----------
    prev_layer = [list(d.keys()) for d in buckets]
    for _ in range(1, max_length):  # ブランク数 1,2,...
        next_layer = [[] for _ in range(max_length + 1)]
        for forms in prev_layer:
            for s in forms:
                for i, ch in enumerate(s):
                    if ch == "t":
                        new_s = s[:i] + "_" + s[i + 1 :]
                        if add(new_s):
                            nblen = len(new_s) - new_s.count("_")
                            next_layer[nblen].append(new_s)
        if all(not layer for layer in next_layer):
            break  # これ以上増えない
        prev_layer = next_layer

    # ---------- dict → list ----------
    result_ordered = [list(d.keys()) for d in buckets]
    return result_ordered


class PatternTag:
    R = "R"  # 述語
    I = "I"  # 項（individual term）
    E = "E"  # 自由型（なんでも通す）
    # ほかにも必要なら追加


class MatchResult(NamedTuple):
    pattern: List[str]  # マッチした構文パターン（例：['I', 'R', 'I']）
    args: List[kono_ast.LaTerm]  # 実際に対応した Term 群（同じ長さ）
    rest: List[kono_ast.LaTerm]  # 残りの AppLine（pattern より右側）


def is_predicate(term: kono_ast.LaTerm) -> bool:
    return isinstance(term, kono_ast.LTerm) and term.tag == "R"


def is_individual(term: kono_ast.LaTerm) -> bool:
    return not isinstance(term, kono_ast.LTerm) or term.tag in ("I", None)


# ------------------------------------------------------------
def identify_appline(
    appline: List[kono_ast.LaTerm], get_patterns
) -> Optional[MatchResult]:
    """
    Parameters
    ----------
    appline : AppLine ノードの中身（List[LaTerm]）
    get_patterns : Callable[[int], List[List[str]]]
        長さ n の構文パターン一覧を返す関数

    Returns
    -------
    MatchResult(pattern, args, rest) or None
    """
    n = len(appline)
    for k in range(n, 0, -1):  # 長いもの優先
        head = appline[:k]
        tail = appline[k:]
        patterns = get_patterns(k)  # 例えば [['I','R'], ['I','I','R']] など

        for pat in patterns:
            assert len(pat) == k
            match = True
            for term, tag in zip(head, pat):
                if tag == PatternTag.R:
                    if not is_predicate(term):  # ex: AppLine が述語項であるか
                        match = False
                        break
                elif tag == PatternTag.I:
                    if not is_individual(term):  # ex: AppLine が項かどうか
                        match = False
                        break
                elif tag == PatternTag.E:
                    continue  # なんでも OK
                else:
                    raise ValueError(f"Unknown tag: {tag}")

            if match:
                return MatchResult(pattern=pat, args=head, rest=tail)

    return None


def Interpret(context, rho, ast):
    """
    エラーの種類
    - Quantifierがscopeを持たない
    - AppLineの省略項(=ゼロ照応)が先行詞を持たない
    """
    # 1) スコープを取得
    scopes_dict = search_scope(ast)

    def rec(ast):
        nonlocal scopes_dict
        match ast:
            case kono_ast.And(left, right):
                return logic.And(rec(left), rec(right))
            case kono_ast.Or(left, right):
                return logic.Or(rec(left), rec(right))
            case kono_ast.Imp(left, right):
                return logic.Imp(rec(left), rec(right))
            case kono_ast.Iff(left, right):
                return logic.Iff(rec(left), rec(right))
            case kono_ast.Not(content):
                return logic.Not(rec(content))
            case kono_ast.Paren(content):
                return rec(content)
            case kono_ast.Sentence(content):
                return rec(content)
            case kono_ast.Discourse(sentences):
                return [rec(s) for s in sentences]
            case kono_ast.Quantified(lq, content) | kono_ast.PullDown(lq, content):
                # ① 同値クラス化（“sub_index”キーごとに分ける関数は既存想定）
                scope_dict = group_by_subindex(
                    scopes_dict[(lq.quantifier, lq.label[0] if lq.label else None)]
                )

                # ② LTerm → Var 置換
                replaced_body, var_order = replace_scope(content, scope_dict)

                # ③ 第1スコープのドメイン要素を生成
                domain = build_first_scope(scope_dict, rec)

                # ④ 量化子ノードを作って上に積む
                return logic.Quantified(
                    quantifier=lq.quantifier,
                    var=var_order,
                    domain=domain,
                    content=rec(replaced_body),
                )
            case kono_ast.AppLine(terms):
                return kono_ast.AppLine([rec(t) for t in terms])
                """
                terms_rec = [rec(t) for t in terms]
                pattern = identify_appline(terms)
                if pattern.count("R") == 1:
                    args = []
                    for i, p in enumerate(pattern):
                        if p == "t":
                            args.append(terms_rec[i])
                        elif p == "_":
                            args.append(rec(free_lterms.pop()))
                    if isinstance(terms[1], logic.Var):
                        pred_name = terms[1]
                        return logic.Predicate("∈", [tuple(args), pred_name])
                    elif isinstance(terms[1].term, kono_ast.Word):
                        pred_name = terms[1].term.name
                        return logic.Predicate(pred_name, args)
                    else:
                        pred_name = terms[1].term
                        return logic.Predicate("∈", [tuple(args), pred_name])"""
            case kono_ast.LTerm(term, sup_indices):
                return rec(term)
            case _:
                return ast

    return rec(ast)


def simplify(ast):
    """
    明らかに簡約化できる部分を簡約化する．
    """

    def simplify_cap(node):
        """
        logic.Cap ノードに対する簡約関数。
        - x ∩ T = x
        - x ∩ x = x
        - ネストした Cap の平坦化
        - 要素が 0 個なら T を返す
        - 要素が 1 個ならその要素を返す
        """
        # 1) 子ノードは既に rec により簡約されている前提で渡される
        flat_args = []
        for arg in node.args:
            # None はスキップ
            if arg is None:
                continue

            # 単位元 T を取り除く
            if isinstance(arg, kono_ast.Class) and arg.name == "T":
                continue

            # ネストした Cap を平坦化
            if isinstance(arg, logic.Cap):
                flat_args.extend(arg.args)
            else:
                flat_args.append(arg)

        # 2) 重複排除 (x ∩ x = x)
        unique_args = []
        for x in flat_args:
            if x not in unique_args:
                unique_args.append(x)

        # 3) 結果に応じて返却
        if len(unique_args) == 0:
            # 全部 T か None のみ → T
            return kono_ast.Class("T")
        if len(unique_args) == 1:
            # 要素がひとつだけ → その要素
            return unique_args[0]
        # 複数の要素が残っていれば交叉ノードを再構築
        return logic.Cap(unique_args)

    def simplify_prod(node):
        """
        logic.Prod ノードに対する簡約関数。
        - すべての引数が T のときは None を返す
        - それ以外は要素ごとに rec を適用して Prod([...]) を返す
        """
        new_args = []
        for arg in node.args:
            simplified = rec(arg)
            # T のみで構成されている場合にはスキップ
            if isinstance(simplified, kono_ast.Class) and simplified.name == "T":
                continue
            new_args.append(simplified)

        if len(new_args) == 0:
            return None
        return logic.Prod(new_args)

    def simplify_quantified(node):
        """
        logic.Quantified ノードに対する簡約関数。
        - 変数束縛の簡約はここでは特に行わず、domain と content を再帰簡約した形を返す
        """
        quantifier, vars_list, domain, content = (
            node.quantifier,
            node.var,
            node.domain,
            node.content,
        )
        new_domain = rec(domain)
        new_content = rec(content)
        return logic.Quantified(quantifier, vars_list, new_domain, new_content)

    def rec(node):
        match node:
            case logic.And(left, right):
                return logic.And(rec(left), rec(right))

            case logic.Or(left, right):
                return logic.Or(rec(left), rec(right))

            case logic.Imp(left, right):
                return logic.Imp(rec(left), rec(right))

            case logic.Iff(left, right):
                return logic.Iff(rec(left), rec(right))

            case logic.Not(content):
                return logic.Not(rec(content))

            case logic.Predicate(name, args):
                return logic.Predicate(name, [rec(arg) for arg in args])

            case logic.Quantified():
                # Quantified(quantifier, vars, domain, content) を想定
                return simplify_quantified(node)

            case logic.Prod():
                return simplify_prod(node)

            case logic.Cap():
                # まず子ノードに rec をかけた上で簡約する
                simplified_args = [rec(arg) for arg in node.args]
                return simplify_cap(logic.Cap(simplified_args))

            case _:
                # 上記以外（Class, Const, 変数ノードなど）はそのまま返す
                return node

    return rec(ast)


def test_01():
    peg = pg.grammar("simple_konomeno.tpeg")
    parser = pg.generate(peg)
    code = "||¬|:|T^∃ T^L ∃. L.-1^∀∃-2∃-1 1 ∃-1.∃-2.∀."
    code = "|||[1^∀-1 dist 2] leq d^∃ → [[1 f] dist [2 f]] leq e^∀-2 ∀-1.∃.∀-2."
    code = "|:|1^L∀ 2^L, 2^L∀ 1^L ∀*. L*.^∀ eq ∀."
    # code = "waka ja hamin ke mikam"
    code = "|[1^∀ prod [2^∀ succ]] eq [[1 prod 2] add 1] ∀*."
    tree = parser(code)
    tree.dump()
    # print("Tree:", tree)
    ast = kono_ast.simp_kono_to_ast(tree)
    print("AST:", ast)
    normed_ast = norm(ast)
    # print("Normed AST:", normed_ast)

    logic_ast = Interpret(None, normed_ast)
    print("Interpreted:", logic_ast)
    print("Simplified:", simplify(logic_ast[0]))
    # print(appline_list())


def test_02():
    peg = pg.grammar("simple_konomeno.tpeg")
    parser = pg.generate(peg)
    tree = parser("|x^∀ eat ∀|")  # 例
    ast = kono_ast.simp_kono_to_ast(tree)
    scopes = search_scope(ast)
    logic_ast = Interpret(None, None, ast)

    # print(scopes)
    print(logic_ast)

    for (q, lab), lterms in scopes.items():
        print(f"{q}{'' if lab is None else lab}  binds  {len(lterms)} term(s)")


if __name__ == "__main__":
    test_02()
