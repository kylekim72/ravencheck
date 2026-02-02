#[crate::check_module(crate)]
#[allow(dead_code)]
mod induction {
    #[annotate]
    fn true_is_true() -> bool {
        true == true
    }

    #[annotate]
    #[should_fail]
    fn true_is_false() -> bool {
        true == false
    }

    #[define]
    enum Nat { Z, S(Box<Nat>) }

    #[annotate]
    fn z_is_z() -> bool {
        Nat::Z == Nat::Z
    }

    #[annotate]
    #[should_fail]
    fn z_is_s() -> bool {
        Nat::Z == Nat::S(Nat::Z)
    }

    #[annotate]
    #[inductive(x: Nat)]
    fn z_is_zi() -> bool {
        Nat::Z == Nat::Z
    }

    #[annotate]
    #[inductive(x: Nat)]
    #[should_fail]
    fn z_is_si() -> bool {
        Nat::Z == Nat::S(x)
    }
    
    #[define]
    #[recursive]
    fn add(x: Nat, y: Nat) -> Nat {
        match x {
            Nat::Z => y,
            Nat::S(x_sub) => Nat::S(Box::new(add(*x_sub, y))),
        }
    }

    #[annotate]
    #[inductive(x: Nat, y: Nat)]
    fn factor_s_right_good() -> Bool {
        add(x,Nat::S(y)) == Nat::S(add(x,y))
    }

    #[annotate]
    #[inductive(x: Nat, y: Nat)]
    #[should_fail]
    fn factor_s_right_oops() -> Bool {
        // This line uses != in place of ==
        add(x,Nat::S(y)) != Nat::S(add(x,y))
    }

    #[annotate]
    #[inductive(x: Nat, y: Nat, z: Nat)]
    #[should_fail]
    fn prop_0() -> bool {
        // Should obviously fail.
        add(y,y) == add(z,z)
    }

    #[annotate]
    #[inductive(x: Nat)]
    #[should_fail]
    fn prop_1() -> bool {
        // Here is a second version that should fail, which quantifies
        // y and z in a different way.
        forall(|y: Nat, z: Nat| {
            add(y,y) == add(z,z)
        })
    }
}
