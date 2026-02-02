axiom Rel : St → St → Type

axiom Func.uniq {A B : St} (f : Func A B) :

    ∀ x y1 y2 : St, St.mem x A →
        Func.app f x y1 → Func.app f x y2 → (y1 =st y2)

axiom Func.from_Rel {A B : St} {P : St → St → Prop}
  (h_tot : ∀ x : St, St.mem x A → ∃ y, St.mem y B ∧ P x y)
  (h_uniq : ∀ x y1 y2 : St, St.mem x A → P x y1 → P x y2 → (y1 =st y2))
  : Func A B


axiom Func.satisfy_Rel {A B : St} {P : St → St → Prop}
  (h_tot : ∀ x : St, St.mem x A → ∃ y, St.mem y B ∧ P x y)
  (h_uniq : ∀ x y1 y2 : St, St.mem x A → P x y1 → P x y2 → (y1 =st y2))
  (x : St) (hx : St.mem x A) :

  P x (Func.app (Func.from_Rel h_tot h_uniq) x)

noncomputable def Func.comp {A B C : St} (g : Func B C) (f : Func A B) :
  Func A C :=

  let P_comp (x z : St) : Prop :=
    z =st (Func.app g (Func.app f x))

  have h_tot : ∀ x : St, St.mem x A →
    ∃ z : St, St.mem z C ∧ P_comp x z := by

    intro x hxmemA
    have ⟨y, hymemB, hyeqfx⟩ := Func.tot f x hxmemA
    have ⟨z, hzmemC, hzeqgy⟩ := Func.tot g y hymemB

    exists z
    constructor
    . exact hzmemC
    . calc
        z =st Func.app g y
            := hzeqgy

        _ =st Func.app g (Func.app f x)
            := Func.app_congr_right hyeqfx

  have h_uniq : ∀ x z1 z2, St.mem x A → P_comp x z1 → P_comp x z2 →
      (z1 =st z2) := by

    intro x z1 z2 hxmemA hz1eqgfx hz2eqgfx

    have ⟨y, hymemB, hyeqfx⟩ := Func.tot f x hxmemA
    have ⟨z, hzmemC, hzeqgy⟩ := Func.tot g y hymemB

    calc
        z1  =st Func.app g (Func.app f x)
            := hz1eqgfx

        _   =st z2
            := St.eq_symm hz2eqgfx

  Func.from_Rel h_tot h_uniq

