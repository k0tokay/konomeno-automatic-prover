import pegtree as pg
import itertools

_skolem_counter = itertools.count(1)  # Skolem関数名用カウンタ
_var_counter = itertools.count(1)      # 変数名カウンタ
_alpha_var_counter = itertools.count(1)   # α変換用変数名カウンタ

"""
pegtreeで得た構文木をASTに変換する
"""
class AST:
    pass

class Var(AST):
    __match_args__ = ("name", "id")
    def __init__(self, name):
        self.name = name
        self.id = next(_var_counter)
        self.name_or_id = "name"
        self.label = name if self.name_or_id == "name" else id
    def __repr__(self):
        # return f'{self.name}_{self.id}' # デバッグ用
        return f'{self.name}'


class Constant(AST):
    __match_args__ = ("name",)
    def __init__(self, name):
        self.name = name
    def __repr__(self):
        return f'{self.name}'

class Predicate(AST):
    __match_args__ = ("name", "args")
    def __init__(self, name, args):
        self.name = name
        self.args = args
    def __repr__(self):
        return f"{self.name}({', '.join(map(str, self.args))})" if self.name != '=' else f"{self.args[0]} = {self.args[1]}"

class Not(AST):
    __match_args__ = ("p",)
    def __init__(self, p):
        self.p = p
    def __repr__(self):
        return f"¬{self.p}"

class And(AST):
    __match_args__ = ("p", "q")
    def __init__(self, p, q):
        self.p = p
        self.q = q
    def __repr__(self):
        return f"({self.p} ∧ {self.q})"

class Or(AST):
    __match_args__ = ("p", "q")
    def __init__(self, p, q):
        self.p = p
        self.q = q
    def __repr__(self):
        return f"({self.p} ∨ {self.q})"

class Imp(AST):
    __match_args__ = ("p", "q")
    def __init__(self, p, q):
        self.p = p
        self.q = q
    def __repr__(self):
        return f"({self.p} → {self.q})"
    

class Iff(AST):
    __match_args__ = ("p", "q")
    def __init__(self, p, q):
        self.p = p
        self.q = q
    def __repr__(self):
        return f"({self.p} ↔ {self.q})"


class ForAll(AST):
    __match_args__ = ("vars", "body")
    def __init__(self, vars, body):
        self.vars = vars # 複数変数をリストで受け取る
        self.body = body
    def __repr__(self):
        return f"∀{', '.join(map(str, self.vars))}. {self.body}"

class Exists(AST):
    __match_args__ = ("vars", "body")
    def __init__(self, vars, body):
        self.vars = vars
        self.body = body
    def __repr__(self):
        return f"∃{', '.join(map(str, self.vars))}. {self.body}"
    
def parse_to_ast(tree):
    env = [{}] # スコープを表現するための環境

    def to_ast(tree):
        tag = tree.getTag()
    
        if tag == 'Theory':
            for c in tree:
                if c.getTag() == 'Formula':
                    return to_ast(c)
            return None
        
        elif tag == 'Formula':
            children = list(tree)
    
            if len(children) == 1:
                return to_ast(children[0]) # 定義上この分岐はおそらく使われない
        
            left = to_ast(children[0])
            op = children[1].getToken()
            right = to_ast(children[2])
        
            if op == '∧':
                return And(left, right)
            elif op == '∨':
                return Or(left, right)
            elif op == '→':
                return Imp(left, right)
            elif op == '↔':
                return Iff(left, right)
            else:
                return None
    
        elif tag == 'Quantified':
            current_type = None
            current_vars = []
            groups = []
            for c in tree[:-1]:
                ctag = c.getTag()
                vname = c[0].getToken()
                if ctag != current_type:
                    if current_type is not None:
                        groups.append((current_type, current_vars))
                    current_type = ctag
                    current_vars = []
                current_vars.append(vname)
            if current_type is not None:
                groups.append((current_type, current_vars))

            env_values = []
            for (qtype, qvars) in groups:
                env_values.append([Var(v) for v in qvars])
                env.append(dict(zip(qvars, env_values[-1])))
        
            formula = to_ast(tree[-1])
        
            for (qtype, qvars), value in reversed(list(zip(groups, env_values))):
                if qtype == 'All':
                    formula = ForAll(value, formula)
                else:
                    formula = Exists(value, formula)
        
            return formula
    
        elif tag == 'Atomic':
            name = None
            args = []
            for c in tree:
                if c.getTag() == 'Predicate':
                    name = c.getToken()
                else:
                    # #Term or #Variable
                    arg_ast = to_ast(c)
                    args.append(arg_ast)
            return Predicate(name, args)
        
        elif tag == 'Equality':
            left = to_ast(tree[0])
            right = to_ast(tree[1])
            return Predicate('=', [left, right])
        
        elif tag == 'Not':
            return Not(to_ast(tree[0]))
    
        elif tag == 'Term':
            if tree[0].getTag() == 'Function':
                # Skolem関数名と引数からPred風に
                function_name = tree[0][0].getToken()
                function_args = [to_ast(arg) for arg in tree[0][1:]]
                return Predicate(function_name, function_args)
            return to_ast(tree[0])
    
        elif tag == 'Variable':
            vname = tree.getToken()
            # 現在のenvスコープを後ろから検索して、一番内側で定義されたVarを取得
            for scope in reversed(env):
                if vname in scope:
                    return scope[vname]
            # 未定義の場合は新しいVarを作成
            var_obj = Var(vname)
            env[-1][vname] = var_obj
            return var_obj
    
        elif tag == 'Constant':
            return Constant(tree.getToken())
    
        else:
            # 未知のタグはそのまま返すか、エラー処理
            return None

    return to_ast(tree)


"""
代入に関する処理
"""
def alpha_var_name(base="X"):
    return f"{base}_α{next(_alpha_var_counter)}"

def free_vars(ast, bound=None):
    """式ast中の自由変数(Varオブジェクト)の集合を返す。
    boundは現在束縛されている変数(Var)の集合またはリスト。"""
    if bound is None:
        bound = set()

    match ast:
        case Var(name):
            # Varがboundにないなら自由変数
            # boundはVarオブジェクト自体を保持すると比較が容易
            # ここではVarのidで比較することも可能
            return {ast} if ast not in bound else set()
        case Constant(_):
            return set()
        case Predicate(name, args):
            s = set()
            for a in args:
                s |= free_vars(a, bound)
            return s
        case Not(p):
            return free_vars(p, bound)
        case And(p,q)|Or(p,q)|Imp(p,q)|Iff(p,q):
            return free_vars(p, bound) | free_vars(q, bound)
        case ForAll(vars, body):
            new_bound = bound | set(vars)
            return free_vars(body, new_bound)
        case Exists(vars, body):
            new_bound = bound | set(vars)
            return free_vars(body, new_bound)
        case _:
            return set()

def alpha_rename(ast, old_var, new_var):
    match ast:
        case Var(name):
            # old_varと同じidならnew_varで置換
            return new_var if ast.label == old_var.label else ast
        case Constant(_):
            return ast
        case Predicate(name, args):
            return Predicate(name, [alpha_rename(a, old_var, new_var) for a in args])
        case Not(p):
            return Not(alpha_rename(p, old_var, new_var))
        case And(p,q) | Or(p,q) | Imp(p,q) | Iff(p,q):
            return type(ast)(alpha_rename(p, old_var, new_var), alpha_rename(q, old_var, new_var))
        case ForAll(vars, body) | Exists(vars, body):
            # 量化子束縛変数をリネーム
            new_vars = []
            changed = False
            for v in vars:
                if v.label == old_var.label:
                    new_vars.append(new_var)
                    changed = True
                else:
                    new_vars.append(v)
            
            if changed:
                return type(ast)(new_vars, alpha_rename(body, old_var, new_var))
            else:
                # old_varがvars中に見つからなければbodyのみ再帰処理
                return type(ast)(new_vars, alpha_rename(body, old_var, new_var))
        case _:
            return ast

def substitute(ast, var, term):
    match ast:
        case Var(name):
            # varと同じidならtermに置換
            return ast if ast.label != var.label else term
        case Constant(_):
            return ast
        case Predicate(name, args):
            return Predicate(name, [substitute(a, var, term) for a in args])
        case Not(p):
            return Not(substitute(p, var, term))
        case And(p,q) | Or(p,q) | Imp(p,q) | Iff(p,q):
            return type(ast)(substitute(p, var, term), substitute(q, var, term))
        # 共通処理: シャドーイングやα変換などは関数化できるとさらに綺麗
        case ForAll(vars, body) | Exists(vars, body):
            # varがvars内でシャドーイングされているか
            if any(v.label == var.label for v in vars):
                # シャドーイングされているので代入しない
                return type(ast)(vars, body)
            else:
                fvars_term = free_vars(term)
                bound_ids = {v.label for v in vars}
                conflict_ids = bound_ids & {fv.label for fv in fvars_term}

                new_vars = vars
                new_body = body
                for v2 in vars:
                    if v2.label in conflict_ids:
                        # α変換
                        new_v = Var(alpha_var_name(v2.name))
                        new_body = alpha_rename(new_body, v2, new_v)
                        new_vars = [new_v if x.label == v2.label else x for x in new_vars]

                return type(ast)(new_vars, substitute(new_body, var, term))
        case _:
            return ast


"""
CNF変換(連言標準形化)に関する処理
"""
def elim_imp(ast):
    match ast:
        case Var(_)|Constant(_)|Predicate(_, _):
            return ast
        case Not(p):
            return Not(elim_imp(p))
        case And(p, q)|Or(p, q):
            return type(ast)(elim_imp(p), elim_imp(q))
        case Imp(p, q):
            p_ = elim_imp(p)
            q_ = elim_imp(q)
            return Or(Not(p_), q_)
        case Iff(p, q):
            p_ = elim_imp(p)
            q_ = elim_imp(q)
            left = Or(Not(p_), q_)
            right = Or(Not(q_), p_)
            return And(left, right)
        case ForAll(vars, body)|Exists(vars, body):
            return type(ast)(vars, elim_imp(body))
        case _:
            return ast

def neg_in(ast):
    match ast:
        case Not(p):
            match p:
                case And(p1, p2):
                    return Or(neg_in(Not(p1)), neg_in(Not(p2)))
                case Or(p1, p2):
                    return And(neg_in(Not(p1)), neg_in(Not(p2)))
                case ForAll(vars, body):
                    # ¬∀x.φ => ∃x.¬φ
                    return neg_in(Exists(vars, Not(body)))
                case Exists(vars, body):
                    # ¬∃x.φ => ∀x.¬φ
                    return neg_in(ForAll(vars, Not(body)))
                case Iff(_, _)|Imp(_, _):
                    # Imp, Iffはelim_impで除去すべきなので、ここで再適用
                    return neg_in(Not(elim_imp(p)))
                case _:
                    return Not(neg_in(p))
        case And(p,q)|Or(p,q):
            return type(ast)(neg_in(p), neg_in(q))
        case ForAll(vars, body)|Exists(vars, body):
            return type(ast)(vars, neg_in(body))
        case _:
            return ast

def skolem(ast, univ=None):
    if univ is None:
        univ = []
    match ast:
        case And(p,q)|Or(p,q):
            return type(ast)(skolem(p, univ), skolem(q, univ))
        case Not(p):
            return Not(skolem(p, univ))
        case ForAll(vars, body):
            # ここでα変換を行わないとダメ
            new_vars = []
            for v in vars:
                if all(v.label != uv.label for uv in univ):
                    univ.append(v)
                    new_vars.append(v)
                else:
                    new_v = Var(alpha_var_name(v.name))
                    body = alpha_rename(body, v, new_v)
                    univ.append(new_v)
                    new_vars.append(new_v)
            return ForAll(new_vars, skolem(body, univ))
        case Exists(vars, body):
            new_body = body
            for ev in vars:
                sk_name = f"sk{next(_skolem_counter)}"
                if univ:
                    # Skolem関数
                    sk_args = univ
                    sk_term = Predicate(sk_name, sk_args)
                else:
                    # Skolem定数
                    sk_term = Constant(sk_name)
                new_body = substitute(new_body, ev, sk_term)
            return skolem(new_body, univ)
        case _:
            return ast

def rm_univ(ast):
    match ast:
        case ForAll(_, body):
            return rm_univ(body)
        case Exists(_, body):
            # Skolem化後は無いはず
            return rm_univ(body)
        case And(p,q):
            return And(rm_univ(p), rm_univ(q))
        case Or(p,q):
            return Or(rm_univ(p), rm_univ(q))
        case Not(p):
            return Not(rm_univ(p))
        case _:
            return ast


def distribute_or(ast):
    match ast:
        case And(p,q):
            return And(distribute_or(p), distribute_or(q))
        case Or(p,q):
            A = distribute_or(p)
            B = distribute_or(q)
            match (A,B):
                case (And(p1, p2), _):
                    return And(distribute_or(Or(p1, B)), distribute_or(Or(p2, B)))
                case (_, And(q1, q2)):
                    return And(distribute_or(Or(A, q1)), distribute_or(Or(A, q2)))
                case _:
                    return Or(A, B)
        case Not(_)|Var(_)|Constant(_)|Predicate(_,_):
            return ast
        # ForAll, Existsはここには残らないはず
        case _:
            return ast

def cnf_convert(ast):
    ast = elim_imp(ast)
    ast = neg_in(ast)
    ast = skolem(ast)
    ast = rm_univ(ast)
    ast = distribute_or(ast)
    return ast

    
def test_01():
    peg = pg.grammar("logic.tpeg")
    parser = pg.generate(peg)
    tree = parser("∃Z∀X. (r(X,Z) ∧ ∀X∃Y.(p(X) → q(Z,Y)))")
    ast = parse_to_ast(tree)
    print("AST:", ast)
    cnf_ast = cnf_convert(ast)
    print("CNF AST:", cnf_ast)

if __name__ == "__main__":
   test_01()
