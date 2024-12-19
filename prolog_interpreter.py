import pegtree as pg
from pegtree.visitor import ParseTreeVisitor
from resolution import *
import argparse

class PrologInterpreter(ParseTreeVisitor):
    def __init__(self, parser):
        ParseTreeVisitor.__init__(self, None)
        self.parser = parser
        self.env = {}

    def eval(self, source, last_query=False):
        tree = self.parser(source)
        ast = parse_prolog_tree_to_ast(tree)
        self.visit(tree)

        if last_query:
            idx = self.env["clauses_num"] - 1
            query = self.env["query"][idx]
            return self.eval_query(idx, query)
        else:
            result_str = "\n".join([self.eval_query(query) for query in self.env["query"]])
            return result_str
        
    def eval_query(self, query):
        result = SLD_resolution(self.env["knowledge_base"], query)
        if result is not None:
            vars = {v for lit in query.negative for v in free_vars(lit)}
            if len(vars) == 0:
                return "true"
            result_str = ", ".join([f"{k} = {v}" for k, v in result.items() if k in vars])
            return result_str
        else:
            return "false"
        
    def acceptProgram(self, tree):
        initial_keys = {"knowledge_base" : [], "query" : []}
        for k, v in initial_keys.items():
            if k not in self.env:
                self.env[k] = v
        for clause in tree:
            self.visit(clause)
        return self.env["knowledge_base"]
    
    def acceptFact(self, tree):
        self.env["knowledge_base"].append(parse_prolog_tree_to_ast(tree))
    def acceptRule(self, tree):
        self.env["knowledge_base"].append(parse_prolog_tree_to_ast(tree))
    def acceptQuery(self, tree):
        self.env["query"].append(parse_prolog_tree_to_ast(tree))


    

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