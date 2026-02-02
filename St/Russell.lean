import St.Subset
-- import Nt.Addition

axiom St.set_exists_universal_specification (P : St → Prop) :
    ∃ S : St,
        ∀ y : St, St.mem y S ↔ P y

theorem St.russell_set_exists_replacement (A : St)
    (P : St → St → Prop) :

    ∃ S : St,
        ∀ y : St, St.mem y S ↔ (∃ x : St, St.mem x A ∧ (P x y)) := by

    let PU (y : St) : Prop := (∃ x : St, St.mem x A ∧ (P x y))

    apply set_exists_universal_specification PU

theorem St.russell_set_exists_specification (A : St) (P : St → Prop) :
    ∃ S : St,
        ∀ y : St, St.mem y S ↔ (St.mem y A ∧ (P y)) := by

    let PU (y : St) : Prop := St.mem y A ∧ (P y)

    apply set_exists_universal_specification PU

theorem St.russell_set_exists_general_uni (A : St) :
    ∃ S : St,
        ∀ y : St, St.mem y S ↔ ∃ x : St, St.mem x A ∧ St.mem y x := by

    let PU (y : St) : Prop := ∃ x : St, St.mem x A ∧ St.mem y x

    apply St.set_exists_universal_specification PU

theorem St.russell_set_exists_pair (a b : St) :
    ∃ S : St,
        ∀ y : St, St.mem y S ↔ ((y =st a) ∨ (y =st b)) := by

    let PU (y : St) : Prop := ((y =st a) ∨ (y =st b))

    apply St.set_exists_universal_specification PU

theorem St.russell_set_exists_singlet (a : St) :
    ∃ S : St,
        ∀ y : St, St.mem y S ↔ (y =st a) := by

    let PU (y : St) : Prop := (y =st a)

    apply St.set_exists_universal_specification PU

theorem St.russell_set_exists_empty :
    ∃ S : St,
        ∀ y : St, St.mem y S ↔ False := by

    let PU (y : St) : Prop := False

    apply St.set_exists_universal_specification PU


/-
def succ : St → St

axiom set_succ (x : St) : (succ x) =st (uni x (singlet x))

theorem russell_set_infinity :
    ∃ S : St,
        St.mem empty S ∧
        ∀ y : St, St.mem y S ↔ St.mem (succ y) S := by

    let PU (y : St) : Prop :=
            (y empty) ∧ ∃ n : St, n =st (succ y)

    apply set_exists_universal_specification PU
-/

















