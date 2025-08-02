import pegtree as pg

PEG_FILE = "simple_konomeno.tpeg"


def parse(code):
    peg = pg.grammar(PEG_FILE)
    parser = pg.generate(peg)
    tree = parser(code)
    return tree


def test_and():
    code = "a , b"
    print(parse(code))


def test_or():
    code = "a ∨ b"
    print(parse(code))


def test_paren():
    code = "(a , b)"
    print(parse(code))


def test_quantified():
    code = "|a^∃ p ∃|"
    print(parse(code))


def test_ZFC_ext():
    code = "|:|T^L-1∀ T^L-2, T^L-2∀ T^L-1 ∀| L-1-2:^∀ eq ∀|"
    print(parse(code))


def test_peano_nonzero():
    code = "|[T^∀ succ] neq lin ∀|"
    print(parse(code))


if __name__ == "__main__":
    test_and()
    test_or()
    test_paren()
    test_quantified()
    test_ZFC_ext()
    test_peano_nonzero()
