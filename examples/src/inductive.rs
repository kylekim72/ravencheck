#[ravencheck::check_module]
#[allow(dead_code)]
mod small_inductive {
    #[define]
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Nat { Z, S(Box<Nat>) }

    #[define]
    #[recursive]
    fn add(a: Nat, b: Nat) -> Nat {
        match a {
            Nat::Z => b,
            Nat::S(a_minus) =>
                // We unbox `a_minus` before calling `add`, and then
                // re-box the output of `add` so that we can wrap it
                // in Nat::S.
                Nat::S(Box::new(add(*a_minus,b))),
        }
    }

    #[annotate]
    #[inductive(a: Nat)]
    fn add_z_left() -> bool {
        add(Nat::Z, a) == a
    }

    #[annotate]
    #[inductive(a: Nat)]
    fn add_z_right() -> bool {
        add(a, Nat::Z) == a
    }
}
