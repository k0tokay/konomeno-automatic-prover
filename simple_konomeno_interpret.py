import itertools

import pegtree as pg

import predicate_logic_ast as logic
import simple_konomeno_ast as kono_ast
from simple_konomeno_ast import rec_template

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


def search_scope(ast, star, kind, label):
    """
    labelに合致するquantifierを持つLTermのlabelを返す．
    """
    scopes = []

    @rec_template
    def rec(ast):
        is_indiv, sup_indices, sub_index = ast.is_indiv, ast.sup_indices, ast.sub_index
        # **最初の**quantifierがkindと一致するかどうかをチェック
        if label is None:
            match = len(sup_indices) > 0 and sup_indices[0].quantifier == kind
        else:
            match = len(sup_indices) > 0 and sup_indices[0].label == label

        if match:
            scopes.append(sub_index)
        if star or not match:
            return rec(ast.term)
        else:
            return ast

    rec(ast)
    return scopes


def replace_scope(ast, kind, label, scopes):
    """
    labelに合致するquantifierを持つLTermを置換する．
    """
    vars_dict = {}
    scopes_dict = {}

    @rec_template
    def rec(ast):
        term, is_indiv, sup_indices, sub_index = (
            ast.term,
            ast.is_indiv,
            ast.sup_indices,
            ast.sub_index,
        )
        if sub_index in scopes:
            if label is None:
                has_corresponding = (
                    len(sup_indices) > 0 and sup_indices[0].quantifier == kind
                )
            else:
                has_corresponding = (
                    len(sup_indices) > 0 and sup_indices[0].label == label
                )

            if has_corresponding:
                sup_indices = sup_indices[1:]

            if sub_index not in scopes_dict:
                scopes_dict[sub_index] = []
            scopes_dict[sub_index].append(
                kono_ast.LTerm(term, is_indiv, sup_indices, sub_index)
            )
            if sub_index not in vars_dict:
                vars_dict[sub_index] = logic.Var("X")
            new_sub_index = next(_label_counter)
            return kono_ast.LTerm(
                vars_dict[sub_index], is_indiv, sup_indices, new_sub_index
            )
        return kono_ast.LTerm(rec(term), is_indiv, sup_indices, sub_index)

    return rec(ast), vars_dict, scopes_dict


# todo: search scopeとreplace scopeは分けないといけない
def search_and_replace(ast, star, kind, label):
    """
    labelに合致するquantifierを持つLTermを返し，そのLTermを置換する．
    """

    scopes = search_scope(ast, star, kind, label)

    if len(scopes) == 0:
        raise ValueError(f"Quantifier {kind}-{label} has no scope in {ast}")

    replaced_ast, new_vars_dict, scopes_dict = replace_scope(ast, kind, label, scopes)
    return replaced_ast, new_vars_dict, scopes_dict

    """
    scopes_dict = {}
    new_vars_dict = {}

    @rec_template
    def rec(ast):
        is_indiv, sup_indices, sub_index = ast.is_indiv, ast.sup_indices, ast.sub_index

        # starがFalseかつlabelがNoneの場合、一度だけmatchしたら以降は置換しない
        if not star and label is None:
            # すでに置換したsub_indexを記録する
            if not hasattr(rec, "matched_sub_indices"):
                rec.matched_sub_indices = set()
        for sup_index in sup_indices:
            match = (label is None and sup_index.quantifier == kind) or (
                label is not None and sup_index.label == label
            )
            if match:
                if not star and label is None:
                    if sub_index in rec.matched_sub_indices:
                        return ast
                    rec.matched_sub_indices.add(sub_index)
                scopes_dict.setdefault(sub_index, []).append(ast)
                new_sup_indices = [
                    x
                    for x in sup_indices
                    if (x.quantifier != kind if label is None else x.label != label)
                ]
                new_var = new_vars_dict.setdefault(sub_index, logic.Var("X"))
                return kono_ast.LTerm(new_var, is_indiv, new_sup_indices, sub_index)
        return ast

    replaced_ast = rec(ast)
    # starがTrueかつlabelがNoneの場合、状態をリセット
    if not star and label is None and hasattr(rec, "matched_sub_indices"):
        del rec.matched_sub_indices
    return replaced_ast, new_vars_dict, scopes_dict"""


def norm(ast):
    """
    ASTをより意味論的に単純な形に変換する．
    """

    normed_ast = add_label(ast)
    return normed_ast


def find_same_lterm(ast, search_label):
    same_lterm = []

    @rec_template
    def rec(ast):
        match ast:
            case kono_ast.LTerm(term, is_indiv, sup_indices, sub_index):
                if sub_index == search_label:
                    same_lterm.append(ast)
                return ast

    rec(ast)
    return same_lterm


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
        if n >= 2:
            add("tR" + "t" * (n - 2))  # tRtt...
        if n % 2 == 1:
            add("t" + "Rt" * (n // 2))  # tRtRt...

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


def identify_appline(terms, search_list=None):
    if search_list is None:
        search_list = appline_list()
    length = len(terms)
    if length > len(search_list):
        raise ValueError(f"Search list is too short: {length} > {len(search_list)}")
    checklist = search_list[length]

    # 今のところは最初のものを返すだけとする．
    return checklist[0]


def Interpret(context, ast):
    """
    命題論理部分のみ対応したKonoméno AST→述語論理ASTの変換。
    context: 現状未使用（将来の拡張用）

    エラーの種類
    - Quantifierがscopeを持たない
    - AppLineの省略項(=ゼロ照応)が先行詞を持たない
    """
    scopes_dict = []
    free_lterms = []

    def rec(ast):
        nonlocal scopes_dict, free_lterms
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
                replaced_ast, new_vars_dict, scopes = search_and_replace(
                    ast, lq.star, lq.quantifier, lq.label
                )

                if len(scopes) == 0:
                    raise ValueError(f"Quantifier {lq} has no scope in {ast}")

                domain_dict = {k: [rec(vi) for vi in v] for k, v in scopes.items()}
                key_order = sorted(domain_dict.keys())
                domain = logic.Prod([logic.Cap(domain_dict[key]) for key in key_order])

                new_vars = [new_vars_dict[key] for key in key_order]
                if len(new_vars) == 1:
                    new_vars = new_vars[0]
                else:
                    new_vars = tuple(new_vars)

                scopes_dict.append((lq, new_vars, scopes))
                return logic.Quantified(
                    lq.quantifier, new_vars, domain, rec(replaced_ast.content)
                )
            case kono_ast.AppLine(terms):
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
                        return logic.Predicate("∈", [tuple(args), pred_name])
            case kono_ast.LTerm(term, is_indiv, sup_indices, sub_index):
                # return kono_ast.LTerm(rec(term), is_indiv, sup_indices, sub_index)
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
    print("Tree:", tree)
    ast = kono_ast.simp_kono_to_ast(tree)
    print("AST:", ast)
    normed_ast = norm(ast)
    print("Normed AST:", normed_ast)

    logic_ast = Interpret(None, normed_ast)
    print("Interpreted:", logic_ast)
    print("Simplified:", simplify(logic_ast[0]))
    # print(appline_list())


if __name__ == "__main__":
    test_01()
