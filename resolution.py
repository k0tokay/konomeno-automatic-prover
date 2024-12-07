def dictexpr2str(expr):
    if isinstance(expr, dict):
        op_str = "predicate" if "predicate" in expr else "function"
        return f"{expr[op_str]}({', '.join([dictexpr2str(arg) for arg in expr['args']])})"
    return expr

def substitute(subs, term):
    # 同時代入
    if isinstance(term, str):
        if term in subs:
            return subs[term]
        return term
    if isinstance(term, dict):
        term = term.copy()
        term["args"] = [substitute(subs, arg) for arg in term["args"]]
        return term

def compose(subs1, subs2):
    # 同時代入の合成
    subs = subs2.copy()
    for var, term in subs1.items():
        subs[var] = substitute(subs2, term)
    return subs

def is_variable(expr):
    return isinstance(expr, str) and (expr[0].isupper() or expr[0] == "_")

def search_vars(expr):
    if isinstance(expr, dict):
        return set().union(*[search_vars(arg) for arg in expr["args"]])
    if is_variable(expr):
        return {expr}
    return set()

def rename_vars(expr, num):
    subs = {}
    def rec(expr):
        nonlocal num
        if isinstance(expr, dict):
            expr = expr.copy()
            expr["args"] = [rec(arg) for arg in expr["args"]]
            return expr
        if is_variable(expr):
            if expr in subs:
                return subs[expr]
            else:
                subs[expr] = f"_a{num}"
                num += 1
                return subs[expr]
        return expr
    return rec(expr), subs, num

def unify(expr1, expr2):
    # 以下のアルゴリズムを参考
    # https://en.wikipedia.org/wiki/Unification_(computer_science)
    exprs = [(expr1, expr2)]
    # print(dictexpr2str(expr1), dictexpr2str(expr2))
    subs = {}
    while exprs:
        expr1, expr2 = exprs.pop()
        if expr1 == expr2:
            continue
        if is_variable(expr1):
            if expr1 in search_vars(expr2):
                return None
            theta = {expr1: expr2}
            subs = compose(subs, theta)
            exprs = [(substitute(theta, arg1), substitute(theta, arg2)) for arg1, arg2 in exprs]
        elif is_variable(expr2):
            if expr2 in search_vars(expr1):
                return None
            theta = {expr2: expr1}
            subs = compose(subs, theta)
            exprs = [(substitute(theta, arg1), substitute(theta, arg2)) for arg1, arg2 in exprs]
        elif isinstance(expr1, dict) and isinstance(expr2, dict):
            if "predicate" in expr1 and "predicate" in expr2:
                op_str = "predicate"
            elif "function" in expr1 and "function" in expr2:
                op_str = "function"
            else:
                return None
            if expr1[op_str] != expr2[op_str] or len(expr1["args"]) != len(expr2["args"]):
                return None
            exprs.extend(zip(expr1["args"], expr2["args"]))
        else:
            return None
    return subs

def SLD_resolution(KB, query):
    # KB: knowledge base
    # query: goal clause
    # return: True if query is provable from KB
    num = 0
    def rec(KB, query):
        nonlocal num
        goals = query["negative"]
        if len(goals) == 0:
            return {}
        current_goal = goals[0]
        for clause in KB.values():
            head = clause["positive"][0]
            head_r, subs_r, num_r = rename_vars(head, num)
            current_goal_r, subs, num_r = rename_vars(current_goal, num_r)
            subs_r = compose(subs_r, subs)
    
            theta = unify(head_r, current_goal_r)
            if theta is not None:
                new_goals = clause["negative"] + (goals[1:] if len(goals) >= 2 else [])
                theta = compose(subs_r, theta)
                num = num_r
                new_goals = [substitute(theta, goal) for goal in new_goals]

                result = rec(KB, {"positive": [], "negative": new_goals})
                if result != None:
                    return compose(theta, result)
        return None
    return rec(KB, query)
    
        