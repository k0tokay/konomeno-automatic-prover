import itertools
from dataclasses import dataclass, field
from typing import List, Optional, Union

import pegtree as pg

_node_counter = itertools.count(1)  # ノード名用カウンタ


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
        self.op = "∧"


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
    label: Optional[str] = None

    def __repr__(self):
        label_str = f"-{self.label}" if self.label else ""
        return f"{self.quantifier}{label_str}"


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
        sup = f"^{''.join(self.sup_indices)}" if self.sup_indices else ""
        sub = f"-{self.sub_index}" if self.sub_index else ""
        if str(self.term) == "T" and self.sub_index:
            return f"{self.sub_index}{indiv}{sup}"
        else:
            return f"{self.term}{indiv}{sup}{sub}"


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
            label = tree[1].getToken() if len(tree) > 1 else None
            return LPDQ(quantifier, label)

        elif tag == "LQ":
            quantifier = tree[0].getToken()
            label = tree[1].getToken() if len(tree) > 1 else None
            return LQ(quantifier, label)

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
                sub_index = tree[0][0].getToken()
            while i < len(tree):
                if tree[i].getTag() == "SupIndex":
                    sup_indices.append(tree[i].getToken())
                elif tree[i].getTag() == "SubIndex":
                    sub_index = tree[i].getToken()
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

        elif tag == "Rel":
            return Rel(tree.getToken())

        elif tag == "Const":
            return Const(tree.getToken())

        elif tag == "Class":
            return Class(tree.getToken())

        elif tag == "Func":
            return Func(tree.getToken())

    return rec(tree)


def test_01():
    peg = pg.grammar("simple_konomeno.tpeg")
    parser = pg.generate(peg)
    code = "|:|T^∃ T^L ∃. L.^∀∃-2∃-1 1 ∃-1."
    code = "|||[x^∀-1 dist a] leq d^∃ → [[x^∀-1 f] dist [a f]] leq e^∀-2 ∀-2.∃.∀-2."
    tree = parser(code)
    tree.dump()
    print("Tree:", tree)
    ast = simp_kono_to_ast(tree)
    print("AST:", ast)


if __name__ == "__main__":
    test_01()
