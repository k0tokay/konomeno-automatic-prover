import pegtree as pg

from simple_konomeno_ast import simp_kono_to_ast

PEG_FILE = "simple_konomeno.tpeg"


def parse_and_ast(code):
    peg = pg.grammar(PEG_FILE)
    parser = pg.generate(peg)
    tree = parser(code)
    return simp_kono_to_ast(tree)


def norm(s):
    return "".join(s.split())


def assert_ast_equiv(code):
    ast = parse_and_ast(code)
    s1 = str(ast)
    print(f"code: {code} -> AST: {s1}")
    assert norm(s1) == norm(code)
    ast2 = parse_and_ast(s1)
    s2 = str(ast2)
    print(f"Reparse: {s1} -> AST: {s2}")
    assert norm(s1) == norm(s2)


def test_and():
    code = "a , b"
    assert_ast_equiv(code)


def test_or():
    code = "a ∨ b"
    assert_ast_equiv(code)


def test_paren():
    code = "(a , b)"
    assert_ast_equiv(code)


def test_quantified():
    code = "|a^∃ p ∃|"
    assert_ast_equiv(code)


def test_ZFC_ext():
    code = "|:|T^L-1^∀ T^L-2, T^L-2^∀ T^L-1 ∀| L-1-2:^∀ eq ∀|"
    assert_ast_equiv(code)


def test_peano_nonzero():
    code = "|[T^∀ succ] neq lin ∀|"
    assert_ast_equiv(code)


if __name__ == "__main__":
    test_and()
    test_or()
    test_paren()
    test_quantified()
    test_ZFC_ext()
    test_peano_nonzero()
