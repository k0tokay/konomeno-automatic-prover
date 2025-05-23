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
    code = "|a ∃."
    assert_ast_equiv(code)


def test_ZFC_ext():
    code = "|:|T^L∀ T^L, T^L∀ T^L ∀*. L*.^∀ eq ∀."
    assert_ast_equiv(code)


def test_ZFC_reg():
    code = "||¬|:|T^∃ T^L ∃. L.-1^∀∃-2∃-1 1 ∃-1.∃-2.∀."
    assert_ast_equiv(code)


def test_peano_nonzero():
    code = "|[T^∀ succ] neq lin ∀."
    assert_ast_equiv(code)


def test_peano_inj():
    code = "|:[neq^∀Fl succ] Fl. neq ∀."
    assert_ast_equiv(code)


def test_peano_addzero():
    code = "|[1^∀ add lin] eq 1 ∀."
    assert_ast_equiv(code)


def test_peano_addsucc():
    code = "|[1^∀ add [2^∀ succ]] eq [[1 add 2] succ] ∀*."
    assert_ast_equiv(code)


def test_peano_prodzero():
    code = "|[1^∀ prod lin] eq lin ∀."
    assert_ast_equiv(code)


def test_peano_prodsucc():
    code = "|[1^∀ prod [2^∀ succ]] eq [[1 prod 2] add 1] ∀*."
    assert_ast_equiv(code)


def test_peano_induction():
    code = "lin pred-1^∀, |[T^∀ succ] 1 ∀. → |T^∀ 1 ∀."
    assert_ast_equiv(code)


def test_eps_delta():
    code = "|||[x^∀-1 dist a] leq d^∃ → [[x^∀-1 f] dist [a f]] leq e^∀-2 ∀-2.∃.∀-2."
    assert_ast_equiv(code)
