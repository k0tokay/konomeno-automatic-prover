import pegtree as pg
from pegtree.visitor import ParseTreeVisitor
from resolution import SLD_resolution, dictexpr2str
import argparse

class PrologInterpreter(ParseTreeVisitor):
    def __init__(self, parser):
        ParseTreeVisitor.__init__(self, None)
        self.parser = parser
        self.env = {}

    def eval(self, source, last_query=False):
        tree = self.parser(source)
        self.visit(tree)

        if last_query:
            idx = self.env["clauses_num"] - 1
            query = self.env["query"][idx]
            return self.eval_query(idx, query)
        else:
            result_str = "\n".join([self.eval_query(idx, query) for idx, query in self.env["query"].items()])
            return result_str
        
    def eval_query(self, idx, query):
        result = SLD_resolution(self.env["knowledge_base"], query)
        if result is not None:
            variables = self.env["variables"][idx]
            if len(variables) == 0:
                return "true"
            inv_variables = {v: k for k, v in variables.items()}
                
            result = {inv_variables[k]: dictexpr2str(v) for k, v in result.items() if k in inv_variables}
            result_str = "\n".join([f"{k} = {v}" for k, v in result.items()])
            return result_str
        else:
            return "false"


    def acceptProgram(self, tree):
        initial_keys = {"knowledge_base" : {}, "query" : {}, "clauses_num" : 0, "variables" : {}, "variables_num" : 0}
        for k, v in initial_keys.items():
            if k not in self.env:
                self.env[k] = v
        
        for clauses in tree:
            idx = self.env["clauses_num"]
            self.env["variables"][idx] = {}
            self.visit(clauses)
            self.env["clauses_num"] += 1

    def acceptFact(self, tree):
        head = self.visit(tree[0])
        idx = self.env["clauses_num"]
        self.env["knowledge_base"][idx] = {
            "positive": [head],
            "negative": []
        }
    
    def acceptRule(self, tree):
        head = self.visit(tree[0])
        body = [self.visit(tree[i]) for i in range(1, len(tree))]
        idx = self.env["clauses_num"]
        self.env["knowledge_base"][idx] = {
            "positive": [head],
            "negative": body
        }

    def acceptQuery(self, tree):
        body = [self.visit(tree[i]) for i in range(0, len(tree))]
        idx = self.env["clauses_num"]
        self.env["query"][idx] = {
            "positive": [],
            "negative": body
        }
    
    def acceptLiteral(self, tree):
        predicate = self.visit(tree[0])
        args = [self.visit(tree[i]) for i in range(1, len(tree))]
        return {
            "predicate": predicate,
            "args": args
        }
    
    def acceptFunctionTerm(self, tree):
        function = self.visit(tree[0])
        args = [self.visit(tree[i]) for i in range(1, len(tree))]
        return {
            "function": function,
            "args": args
        }
    
    def acceptFunction(self, tree):
        token = tree.getToken()
        return token
    
    def acceptPredicate(self, tree):
        token = tree.getToken()
        return token
    
    def acceptVariable(self, tree):
        clause_idx = self.env["clauses_num"]

        token = tree.getToken()
        if token in self.env["variables"][clause_idx]:
            renamed = self.env["variables"][clause_idx][token]
        else:
            renamed = f"_{self.env['variables_num']}"
            self.env['variables_num'] += 1
            self.env["variables"][clause_idx][token] = renamed
        
        return renamed
    
    def acceptConstant(self, tree):
        token = tree.getToken()
        return token

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Prolog interpreter")
    parser.add_argument("-f", "--filepath", type=str, default="prolog_examples/socrates.pl", help="Prolog source code file path")
    args = parser.parse_args()

    peg = pg.grammar("prolog.tpeg")
    parser = pg.generate(peg)

    prolog = PrologInterpreter(parser)

    with open(args.filepath) as f:
        code = f.read()

    result = prolog.eval(code)

    print(result)

    while True:
        prompt = input("?- ")
        if prompt == "exit.":
            break
        result = prolog.eval(f"?- {prompt}", last_query=True)
        print(result)