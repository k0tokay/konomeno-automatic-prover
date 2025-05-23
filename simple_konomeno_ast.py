import itertools
from dataclasses import dataclass, field
from typing import List, Optional, Union

import pegtree as pg

import predicate_logic_ast as logic


@dataclass
class AST:
    def __repr__(self):
        return str(self)


@dataclass(repr=False)
class BinaryOp(AST):
    left: AST
    right: AST
    op: str = field(init=False)

    def __repr__(self):
        return f"{self.left} {self.op} {self.right}"


@dataclass(repr=False)
class And(BinaryOp):
    def __post_init__(self):
        self.op = ","


@dataclass(repr=False)
class Or(BinaryOp):
    def __post_init__(self):
        self.op = "∨"


@dataclass(repr=False)
class Imp(BinaryOp):
    def __post_init__(self):
        self.op = "→"


@dataclass(repr=False)
class Iff(BinaryOp):
    def __post_init__(self):
        self.op = "↔"


@dataclass
class Not(AST):
    content: AST

    def __repr__(self):
        return f"¬{self.content}"


@dataclass
class Quantifier(AST):
    quantifier: str
    star: bool = False
    label: Optional[str] = None

    def __repr__(self):
        label_str = f"-{self.label}" if self.label else ""
        star_str = "*" if self.star else ""
        return f"{self.quantifier}{star_str}{label_str}"


@dataclass(repr=False)
class LQ(Quantifier):
    pass


@dataclass(repr=False)
class LPDQ(Quantifier):
    pass


@dataclass
class Quantified(AST):
    lq: LQ
    content: AST

    def __repr__(self):
        return f"|{self.content} {self.lq}."


@dataclass
class Paren(AST):
    content: AST

    def __repr__(self):
        return f"({self.content})"


@dataclass
class AppLine(AST):
    terms: List[Union["LTerm", "Rel"]]

    def __repr__(self):
        return " ".join(map(str, self.terms))


@dataclass
class LTerm(AST):
    term: AST
    is_indiv: bool = False
    sup_indices: List[str] = None
    sub_index: Optional[str] = None

    def __post_init__(self):
        if self.sup_indices is None:
            self.sup_indices = []

    def __repr__(self):
        indiv = "ι" if self.is_indiv else ""
        sup = f"^{''.join(map(str, self.sup_indices))}" if self.sup_indices else ""
        sub = f"-{self.sub_index}" if self.sub_index else ""
        if str(self.term) == "T" and self.sub_index:
            return f"{self.sub_index}{indiv}{sup}"
        else:
            return f"{self.term}{indiv}{sub}{sup}"


@dataclass
class Word(AST):
    name: str

    def __repr__(self):
        return self.name


@dataclass(repr=False)
class Const(Word):
    pass


@dataclass(repr=False)
class Class(Word):
    pass


@dataclass(repr=False)
class Rel(Word):
    pass


@dataclass(repr=False)
class Func(Word):
    pass


@dataclass
class Function(AST):
    name: Func
    args: List[LTerm]

    def __repr__(self):
        arg_list = [self.args[0], self.name, *self.args[1:]]
        return f"[{' '.join(map(str, arg_list))}]"


@dataclass
class PullDown(AST):
    lpdq: LPDQ
    content: AST

    def __repr__(self):
        return f":{self.content} {self.lpdq}."


@dataclass
class Discourse(AST):
    sentences: List["Sentence"]

    def __repr__(self):
        return "; ".join(map(str, self.sentences))


@dataclass
class Sentence(AST):
    content: AST

    def __repr__(self):
        return str(self.content)


def simp_kono_to_ast(tree):
    def rec(tree):
        tag = tree.getTag()

        if tag == "Discourse":
            sentences = [rec(s) for s in tree]
            return Discourse(sentences)

        elif tag == "Sentence":
            return Sentence(rec(tree[0]))

        elif tag == "Iff":
            left = rec(tree.get("left"))
            right = rec(tree.get("right"))
            return Iff(left, right)

        elif tag == "Imp":
            left = rec(tree.get("left"))
            right = rec(tree.get("right"))
            return Imp(left, right)

        elif tag == "Or":
            left = rec(tree.get("left"))
            right = rec(tree.get("right"))
            return Or(left, right)

        elif tag == "And":
            left = rec(tree.get("left"))
            right = rec(tree.get("right"))
            return And(left, right)

        elif tag == "Literal":
            result = rec(tree[-1])
            for _ in range(len(tree) - 1):
                result = Not(result)
            return result

        elif tag == "LPDQ":
            quantifier = tree[0].getToken()
            star = len(tree) > 1 and tree[1].getToken() == "*"
            label = tree[-1].getTag() == "Label" and int(tree[-1].getToken()) or None
            return LPDQ(quantifier, star, label)

        elif tag == "LQ":
            quantifier = tree[0].getToken()
            star = len(tree) > 1 and tree[1].getToken() == "*"
            label = tree[-1].getTag() == "Label" and int(tree[-1].getToken()) or None
            return LQ(quantifier, star, label)

        elif tag == "Quantified":
            lq = rec(tree[1][0])
            content = rec(tree[0])
            return Quantified(lq, content)

        elif tag == "Paren":
            return Paren(rec(tree[0]))

        elif tag == "AppLine":
            terms = [rec(t) for t in tree]
            return AppLine(terms)

        elif tag == "LTerm":
            term = rec(tree[0])
            is_indiv = len(tree) > 1 and tree[1].getToken() == "ι"
            sup_indices = []
            sub_index = None
            i = 2 if is_indiv else 1
            if len(tree[0]) > 0 and tree[0][0].getTag() == "Label":
                sub_index = int(tree[0][0].getToken())  # int型に変換
            while i < len(tree):
                if tree[i].getTag() == "SupIndex":
                    sup_indices.append(rec(tree[i][0]))
                elif tree[i].getTag() == "SubIndex":
                    sub_index = int(tree[i].getToken())  # int型に変換
                i += 1
            return LTerm(term, is_indiv, sup_indices, sub_index)

        elif tag == "PullDown":
            lpdq = rec(tree[1][0])
            content = rec(tree[0])
            return PullDown(lpdq, content)

        elif tag == "Function":
            name = rec(tree[1])
            args = [rec(arg) for arg in [tree[0]] + tree[2:]]
            return Function(name, args)

        elif tag == "Term":
            if tree.getToken() == "T":
                return Class("T")
            if len(tree) > 0:
                if tree[0].getTag() == "Label":
                    return Class("T")
                else:
                    return rec(tree[0])

        elif tag == "Word":
            return Word(tree.getToken())

        elif tag == "Func":
            return Func(tree.getToken())

    return rec(tree)


def rec_template(func):
    def rec(ast, *args, **kwargs):
        match ast:
            case Discourse(sentences):
                return type(ast)([rec(s, *args, **kwargs) for s in sentences])
            case Sentence(content):
                return type(ast)(rec(content, *args, **kwargs))
            case And(left, right):
                return type(ast)(
                    rec(left, *args, **kwargs), rec(right, *args, **kwargs)
                )
            case Or(left, right):
                return type(ast)(
                    rec(left, *args, **kwargs), rec(right, *args, **kwargs)
                )
            case Imp(left, right):
                return type(ast)(
                    rec(left, *args, **kwargs), rec(right, *args, **kwargs)
                )
            case Iff(left, right):
                return type(ast)(
                    rec(left, *args, **kwargs), rec(right, *args, **kwargs)
                )
            case Not(content):
                return type(ast)(rec(content, *args, **kwargs))
            case Paren(content):
                return type(ast)(rec(content, *args, **kwargs))
            case Quantified(lq, content):
                return type(ast)(lq, rec(content, *args, **kwargs))
            case PullDown(lpdq, content):
                return type(ast)(lpdq, rec(content, *args, **kwargs))
            case AppLine(terms):
                return type(ast)([rec(t, *args, **kwargs) for t in terms])
            case LTerm(term, is_indiv, sup_indices, sub_index):
                return func(
                    type(ast)(
                        rec(term, *args, **kwargs), is_indiv, sup_indices, sub_index
                    ),
                    *args,
                    **kwargs,
                )
            case _:
                return ast

    return rec


def max_label(ast):
    """
    ASTの全てのLTermのlabelの最大値を返す．
    """
    max_label = 0

    @rec_template
    def rec(ast):
        match ast:
            case LTerm(term, is_indiv, sup_indices, sub_index):
                nonlocal max_label
                if sub_index is not None:
                    max_label = max(max_label, sub_index)
            case _:
                pass

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
            case LTerm(term, is_indiv, sup_indices, sub_index):
                if sub_index is None:
                    sub_index = next(_label_counter)
                return LTerm(term, is_indiv, sup_indices, sub_index)

    return rec(ast)


def search_scope(ast, star, kind, label):
    """
    labelに合致するquantifierを持つLTermを返す．labelがない場合はkindで探す．
    """
    scopes = []

    @rec_template
    def rec(ast):
        match ast:
            case LTerm(term, is_indiv, sup_indices, sub_index):
                for sup_index in sup_indices:
                    if label is None:
                        if sup_index.quantifier == kind:
                            scopes.append(ast)
                            if not star:
                                return ast
                    else:
                        if sup_index.label is not None and sup_index.label == label:
                            scopes.append(ast)
                            if not star:
                                return ast
                return ast

    rec(ast)
    return scopes


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
            case LTerm(term, is_indiv, sup_indices, sub_index):
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


def identity_appline(terms, search_list=None):
    if search_list is None:
        search_list = appline_list()
    length = len(terms)
    if length > len(search_list):
        raise ValueError(f"Search list is too short: {length} > {len(search_list)}")
    checklist = search_list[length]

    # 今のところは最初のものを返すだけとする．
    return checklist[0]


def Interpret(context, kono_ast):
    """
    命題論理部分のみ対応したKonoméno AST→述語論理ASTの変換。
    context: 現状未使用（将来の拡張用）
    """
    scopes_dict = []  # unhashableなのでTupleで入れる
    free_lterms = []

    def rec(ast):
        nonlocal free_lterms
        match ast:
            case And(left, right):
                return logic.And(rec(left), rec(right))
            case Or(left, right):
                return logic.Or(rec(left), rec(right))
            case Imp(left, right):
                return logic.Imp(rec(left), rec(right))
            case Iff(left, right):
                return logic.Iff(rec(left), rec(right))
            case Not(content):
                return logic.Not(rec(content))
            case Paren(content):
                return rec(content)
            case Sentence(content):
                return rec(content)
            case Discourse(sentences):
                return [rec(s) for s in sentences]
            case Quantified(lq, content):
                scopes = search_scope(ast, lq.star, lq.quantifier, lq.label)
                scopes_dict.append((lq, scopes))
                free_lterms += scopes
                return logic.Quantified(lq.quantifier, logic.Var("X"), rec(content))
            case PullDown(lpdq, content):
                scopes = search_scope(ast, lpdq.star, lpdq.quantifier, lpdq.label)
                scopes_dict.append((lpdq, scopes))
                free_lterms += scopes
                return logic.Quantified(lpdq.quantifier, logic.Var("X"), rec(content))
            case AppLine(terms):
                print(f"terms: {terms}")
                terms_rec = [rec(t) for t in terms]
                pattern = identity_appline(terms)
                if pattern.count("R") == 1:
                    args = []
                    for i, p in enumerate(pattern):
                        if p == "t":
                            args.append(terms_rec[i])
                        elif p == "_":
                            args.append(rec(free_lterms.pop()))
                    if isinstance(terms[1].term, Word):
                        pred_name = terms[1].term.name
                        return logic.Predicate(pred_name, args)
                    else:
                        pred_name = terms[1].term
                        return logic.Predicate("∈", tuple(args), pred_name)
            case LTerm(term, is_indiv, sup_indices, sub_index):
                if sub_index in map(lambda x: x[0].label, scopes_dict):
                    # free variableから削除
                    free_lterms = [t for t in free_lterms if t.sub_index != sub_index]
                    return logic.Var(f"X{sub_index}")
                else:
                    free_lterms.append(ast)
                    return rec(term)
            case _:
                return ast

    return rec(kono_ast)


def test_01():
    peg = pg.grammar("simple_konomeno.tpeg")
    parser = pg.generate(peg)
    code = "||¬|:|T^∃ T^L ∃. L.-1^∀∃-2∃-1 1 ∃-1.∃-2.∀."
    # code = "|||[x^∀-1 dist a] leq d^∃ → [[x^∀-1 f] dist [a f]] leq e^∀-2 ∀-2.∃.∀-2."
    # code = "|:|T^L∀ T^L, T^L∀ T^L ∀*. L*.^∀ eq ∀."
    tree = parser(code)
    tree.dump()
    print("Tree:", tree)
    ast = simp_kono_to_ast(tree)
    print("AST:", ast)
    normed_ast = norm(ast)
    print("Normed AST:", normed_ast)
    print(Interpret(None, normed_ast))
    # print(appline_list())


if __name__ == "__main__":
    test_01()
