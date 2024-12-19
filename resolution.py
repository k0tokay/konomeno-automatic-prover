from predicate_logic_ast import *

_skolem_counter = itertools.count(1)  # Skolem関数名用カウンタ
_var_counter = itertools.count(1)      # 変数名カウンタ
_alpha_var_counter = itertools.count(1)   # α変換用変数名カウンタ

def unify(expr1, expr2):
    # 以下のアルゴリズムを参考
    # https://en.wikipedia.org/wiki/Unification_(computer_science)
    exprs = [(expr1, expr2)]
    # print(dictexpr2str(expr1), dictexpr2str(expr2))
    subs = {}
    
    while exprs:
        expr1, expr2 = exprs.pop()
        if str(expr1) == str(expr2): # オブジェクトとしては等しくない
            continue
        if isinstance(expr1, Var):
            if expr1.label in [v.label for v in free_vars(expr2)]:
                return None
            theta = {expr1: expr2}
            subs = compose(subs, theta)
            exprs = [(simul_subs(theta, arg1), simul_subs(theta, arg2)) for arg1, arg2 in exprs]
        elif isinstance(expr2, Var): # expr1の場合と対称的に処理する
            if expr2.label in [v.label for v in free_vars(expr1)]:
                return None
            theta = {expr2: expr1}
            subs = compose(subs, theta)
            exprs = [(simul_subs(theta, arg1), simul_subs(theta, arg2)) for arg1, arg2 in exprs]
        elif isinstance(expr1, Predicate) and isinstance(expr2, Predicate):
            if expr1.name != expr2.name or len(expr1.args) != len(expr2.args):
                return None
            exprs.extend(zip(expr1.args, expr2.args))
        else:
            return None
    return subs

def SLD_resolution(KB, query):
    # KB: knowledge base
    # query: goal clause
    # return: True if query is provable from KB
    def make_unique_vars(clause):
        vars = free_vars(clause)
        subs = {v: Var(f"{v.label}_α{next(_alpha_var_counter)}") for v in vars}
        return simul_subs(subs, clause), subs
    
    KB, KB_subs = zip(*[make_unique_vars(clause) for clause in KB])
    query, query_subs = make_unique_vars(query)

    def rec(KB, query):
        global _alpha_var_counter
        
        goals = query.negative
        if len(goals) == 0:
            return {}
        current_goal = goals[0]

        for clause in KB:
            head = clause.positive[0]
            vars = free_vars(head)
            subs1 = {v: Var(f"{v}_α{next(_alpha_var_counter)}") for v in vars}
            # head_r, subs_r, num_r = rename_vars(head, num)
            head_r = simul_subs(subs1, head)
            vars = free_vars(current_goal)
            subs2 = {v: Var(f"{v}_α{next(_alpha_var_counter)}") for v in vars}
            # current_goal_r, subs_r, num_r = rename_vars(current_goal, num_r)
            current_goal_r = simul_subs(subs2, current_goal)
            subs_r = compose(subs1, subs2)
            theta = unify(head_r, current_goal_r)
            if theta is not None:
                new_goals = clause.negative + (goals[1:] if len(goals) >= 2 else [])
                theta = compose(subs_r, theta)
                new_goals = [simul_subs(theta, goal) for goal in new_goals]
                new_goals = Clause([], new_goals)

                result = rec(KB, new_goals)
                if result is not None:
                    return compose(theta, result)
        return None
    return compose(query_subs, rec(KB, query))

def test_01():
    # Test for unify
    expr1 = Predicate("P", [Var("x"), Var("y"), Var("z")])
    expr2 = Predicate("P", [Var("a"), Var("b"), Var("c")])
    subs = unify(expr1, expr2)
    print(subs)
    print(simul_subs(subs, expr1))
    print(simul_subs(subs, expr2))

if __name__ == "__main__":
    test_01()
    
        