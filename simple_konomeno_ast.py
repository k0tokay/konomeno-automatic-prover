from dataclasses import dataclass, field
from typing import List, Union


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
    label: List[str]

    def __repr__(self):
        if self.label:
            label_str = "".join([f"-{l}" for l in self.label])
        else:
            label_str = ""
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
        return f"|{self.content} {self.lq}|"


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
    sup_indices: List[str] = None

    def __post_init__(self):
        if self.sup_indices is None:
            self.sup_indices = []

    def __repr__(self):
        sup = f"^{''.join(map(str, self.sup_indices))}" if self.sup_indices else ""
        return f"{self.term}{sup}"


@dataclass
class LaTerm(AST):
    term: AST
    alpha: str

    def __repr__(self):
        if self.alpha:
            return f"{self.term}_{self.alpha}"
        else:
            return f"{self.term}"


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
        return f":{self.content} {self.lpdq}:"


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

        elif tag == "Quantified":
            lq = rec(tree[1][0])
            content = rec(tree[0])
            return Quantified(lq, content)

        elif tag == "PullDown":
            lpdq = rec(tree[1][0])
            content = rec(tree[0])
            return PullDown(lpdq, content)

        elif tag == "LPDQ":
            quantifier = tree[0].getToken()
            if tree[-1].getTag() == "Label":
                return LPDQ(quantifier, [int(tree[-1].getToken())])
            else:
                return LPDQ(quantifier, [])

        elif tag == "LQ":
            quantifier = tree[0].getToken()
            if tree[-1].getTag() == "Label":
                return LQ(quantifier, [int(tree[-1].getToken())])
            else:
                return LQ(quantifier, [])

        elif tag == "LsPDQ":
            quantifier = tree[0].getToken()
            labels = [
                int(tree[i].getToken())
                for i in range(1, len(tree))
                if tree[i].getTag() == "Label"
            ]
            return LPDQ(quantifier, labels)

        elif tag == "LsQ":
            quantifier = tree[0].getToken()
            labels = [
                int(tree[i].getToken())
                for i in range(1, len(tree))
                if tree[i].getTag() == "Label"
            ]
            return LQ(quantifier, labels)

        elif tag == "Paren":
            return Paren(rec(tree[0]))

        elif tag == "AppLine":
            terms = [rec(t) for t in tree]
            return AppLine(terms)

        elif tag == "LaTerm":
            print(tree)
            term = rec(tree[0])
            alpha = tree[1].getToken() if len(tree) > 1 else None
            return LaTerm(term, alpha)

        elif tag == "SimpleLTerm":
            term = rec(tree[0])
            return LTerm(term, sup_indices=[])

        elif tag == "ComplexLTerm":
            term = rec(tree[0])
            sup_indices = [rec(t) for t in tree[1:]]
            lterm = term
            for sup_index in sup_indices:
                lterm = LTerm(lterm, [sup_index])
            return lterm

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
            case Function(name, func_args):
                return type(ast)(name, [rec(arg, *args, **kwargs) for arg in func_args])
            case LTerm(term, sup_indices):
                return func(ast, *args, **kwargs)
            case _:
                return ast

    return rec


def rec_template_with_quantifier(func):
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
                return func(ast, *args, **kwargs)
            case PullDown(lpdq, content):
                return func(ast, *args, **kwargs)
            case AppLine(terms):
                return type(ast)([rec(t, *args, **kwargs) for t in terms])
            case Function(name, func_args):
                return type(ast)(name, [rec(arg, *args, **kwargs) for arg in func_args])
            case LaTerm(term, alpha):
                return type(ast)(rec(term, *args, **kwargs), alpha)
            case LTerm(term, sup_indices):
                return func(ast, *args, **kwargs)
            case _:
                return ast

    return rec
