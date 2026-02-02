import St.Composition


def Func.bij {A B : St} (f : Func A B) : Prop :=
    Func.inj f ∧ Func.onto f

axiom Func.exists_from_rel {A B : St} (P : St → St → Prop)
  (h_tot : ∀ x : St, St.mem x A → ∃ y, St.mem y B ∧ P x y)
  (h_uniq : ∀ x y1 y2 : St, St.mem x A → St.mem y1 B → St.mem y2 B →
    P x y1 → P x y2 → (y1 =st y2)) :

    ∃ f : Func A B, ∀ x, (hxmemA : St.mem x A) →
        Func.app f x =st Classical.choose (h_tot x hxmemA)

noncomputable def Func.from_rel {A B :St} (P : St → St → Prop)
  (h_tot : ∀ x : St, St.mem x A → ∃ y, St.mem y B ∧ P x y)
  (h_uniq : ∀ x y1 y2 : St, St.mem x A → St.mem y1 B → St.mem y2 B →
    P x y1 → P x y2 → (y1 =st y2)) : Func A B :=

    Classical.choose (Func.exists_from_rel P h_tot h_uniq)

theorem Func.app_from_rel {A B : St} (P : St → St → Prop)
  (h_tot : ∀ x : St, St.mem x A → ∃ y, St.mem y B ∧ P x y)
  (h_uniq : ∀ x y1 y2 : St, St.mem x A → St.mem y1 B → St.mem y2 B →
    P x y1 → P x y2 → (y1 =st y2)) :

    ∀ x, (hxmemA : St.mem x A) →
        Func.app (Func.from_rel P h_tot h_uniq) x =st
            Classical.choose (h_tot x hxmemA)
    :=

    Classical.choose_spec (Func.exists_from_rel P h_tot h_uniq)

axiom Func.exists_inv {A B : St}
    (f : Func A B) (hfbij : Func.bij f) :

    ∃ f' : Func B A,
        ∀ x y : St, St.mem x A → St.mem y B →
            y =st Func.app f x → x =st Func.app f' y

noncomputable def Func.inv {A B : St}
    (f : Func A B) (hfbij : Func.bij f) : Func B A :=

    Classical.choose (Func.exists_inv f hfbij)

theorem Func.app_inv {A B : St} (f : Func A B) (hfbij : Func.bij f) :

    ∀ x y : St, St.mem x A → St.mem y B →
        y =st Func.app f x →
            x =st Func.app (Func.inv f hfbij) y :=

    Classical.choose_spec (Func.exists_inv f hfbij)

axiom Func.bij_congr {A B : St} {f g : Func A B} :

    (f =func g) → (Func.bij f ↔ Func.bij g)

axiom Func.inv_congr_left {A B : St}
    {f g : Func A B} {hfbij : Func.bij f} :

    (hfeqg : f =func g) →

        let hgbij := (Func.bij_congr hfeqg).mp hfbij
        Func.inv f hfbij =func Func.inv g hgbij


theorem Func.empty_empty_bijective (f : Func St.empty St.empty) :
    Func.bij f := by

    constructor
    · apply (Func.empty_inj f)

    · apply (Func.is_onto f).mpr
      intro y hymemEmp

      exfalso
      apply (St.mem_empty y).mp
      exact hymemEmp


theorem Func.canc_bij_ff' {A B : St} (f : Func A B)
    (f' : Func B A) (hfbij : Func.bij f) :

    f' =func Func.inv f hfbij →
        ∀ y, St.mem y B →
            Func.app f (Func.app f' y) =st y := by

    intro hf'eqfinv y hymemB

    have ⟨hfinj, hfonto⟩ := hfbij

    have ⟨x, hxmemA, hyeqfx⟩ := (Func.is_onto f).mp hfonto y hymemB

    have hxeqf'y := Func.app_inv f hfbij x y hxmemA hymemB hyeqfx
 
    calc
        Func.app f (Func.app f' y)
            =st Func.app f (Func.app (Func.inv f hfbij) y)
                := Func.app_congr_right (
                    Func.app_congr_left hf'eqfinv)

        _   =st Func.app f x
                := Func.app_congr_right (St.eq_symm hxeqf'y)

        _   =st y
                := St.eq_symm hyeqfx


theorem Func.canc_bij_f'f {A B : St} (f : Func A B) (f' : Func B A)
    (hfbij : Func.bij f) :

    f' =func Func.inv f hfbij →
        ∀ x, St.mem x A →
            Func.app f' (Func.app f x) =st x := by

    intro hf'eqfinv x hxmemA

    have ⟨hfinj, hfonto⟩ := hfbij

    have ⟨y, hymemB, hyeqfx⟩ := Func.tot f x hxmemA

    have hxeqf'y := Func.app_inv f hfbij x y hxmemA hymemB hyeqfx

    calc
        Func.app f' (Func.app f x)
            =st Func.app f' y
                := Func.app_congr_right (St.eq_symm hyeqfx)

        _   =st Func.app (Func.inv f hfbij) y
                := Func.app_congr_left hf'eqfinv

        _   =st x
                := St.eq_symm hxeqf'y



theorem Func.inv_bij {A B : St} (f: Func A B) (f' : Func B A)
    (hfbij : Func.bij f) (hf'eqfinv : f' =func Func.inv f hfbij) :

    Func.bij f' := by

    have ⟨hfinj, hfonto⟩ := hfbij

    constructor
    · apply (Func.is_inj f').mpr
      intro y y' hymemB hy'memB hf'yeqf'y'

      calc
        y =st Func.app f (Func.app f' y)
            := St.eq_symm (
                Func.canc_bij_ff' f f' hfbij hf'eqfinv y hymemB)

        _ =st Func.app f (Func.app f' y')
            := Func.app_congr_right hf'yeqf'y'

        _ =st y'
            := Func.canc_bij_ff' f f' hfbij hf'eqfinv y' hy'memB

    · apply (Func.is_onto f').mpr
      intro x hxmemA

      have ⟨y, hymemB, hyeqfx⟩ := Func.tot f x hxmemA

      exists y

      constructor
      · exact hymemB
      · calc
            x =st Func.app f' (Func.app f x)
                := St.eq_symm (
                    Func.canc_bij_f'f f f' hfbij hf'eqfinv x hxmemA)

            _ =st Func.app f' y
                := Func.app_congr_right (St.eq_symm hyeqfx)


theorem Func.inv_f'_eq_f {A B : St} (f: Func A B) (f' : Func B A)
    (hfbij : Func.bij f) (hf'eqfinv : f' =func Func.inv f hfbij)
    (hf'bij : Func.bij f' := Func.inv_bij f f' hfbij hf'eqfinv) :

    f =func (Func.inv f' hf'bij) := by

    apply (Func.ext f (Func.inv f' hf'bij)).mp

    intro x hxmemA

    have ⟨y, hymemB, hyeqfx⟩ := Func.tot f x hxmemA

    have hxeqf'y :=
        Func.app_inv f hfbij x y hxmemA hymemB hyeqfx

    have hfinvbij : Func.bij (Func.inv f hfbij) :=
        (Func.bij_congr hf'eqfinv).mp hf'bij

    have hyeqf''x :=
        Func.app_inv (Func.inv f hfbij) hfinvbij y x
            hymemB hxmemA hxeqf'y

    calc
        Func.app f x
            =st y
                := St.eq_symm hyeqfx

        _   =st Func.app (Func.inv (Func.inv f hfbij) hfinvbij) x
                := hyeqf''x

        _   =st Func.app (Func.inv f' hf'bij) x
                := Func.app_congr_left (
                    Func.inv_congr_left (
                        Func.eq_symm hf'eqfinv))


theorem Func.comp_bij_if_fg_bij {A B C : St}
    (f : Func A B) (g : Func B C)
    (hfbij : Func.bij f) (hgbij : Func.bij g) :

    Func.bij (Func.comp g f) := by

    have ⟨hfinj, hfonto⟩ := hfbij
    have ⟨hginj, hgonto⟩ := hgbij

    have hgfinj := Func.comp_inj f g hfinj hginj
    have hgfonto := Func.comp_onto f g hfonto hgonto

    constructor
    · exact hgfinj
    · exact hgfonto



theorem comp_inv_eq_f_inv_g_inv {A B C : St}
    (f : Func A B) (g : Func B C)
    (hfbij : Func.bij f) (hgbij : Func.bij g)
    (hgfbij : Func.bij (Func.comp g f) :=
        Func.comp_bij_if_fg_bij f g hfbij hgbij) :

    Func.inv (Func.comp g f) hgfbij =func
        Func.comp (Func.inv f hfbij) (Func.inv g hgbij) := by

    let g' := (Func.inv g hgbij)
    let f' := (Func.inv f hfbij)
    let «(gf)'» := (Func.inv (Func.comp g f) hgfbij)

    have hf'eqfinv : f' =func Func.inv f hfbij := by rfl
    have hf'bij := Func.inv_bij f f' hfbij hf'eqfinv

    have hg'eqginv : g' =func Func.inv g hgbij := by rfl
    have hg'bij := Func.inv_bij g g' hgbij hg'eqginv

    apply (Func.ext «(gf)'» (Func.comp f' g')).mp

    intro z hzmemC

    have ⟨hgfinj, hgfonto⟩ := hgfbij

    have ⟨x, hxmemA, hzeqgfx⟩ :=
        (Func.is_onto (Func.comp g f)).mp hgfonto z hzmemC

    have «hxeq(gf)'z» :=
        Func.app_inv (Func.comp g f) hgfbij x z hxmemA hzmemC hzeqgfx

    have ⟨y, hymemB, hyeqfx⟩ := Func.tot f x hxmemA

    have ⟨z', hz'memC, hz'eqgy⟩ := Func.tot g y hymemB

    have hxeqf'y := Func.app_inv f hfbij x y hxmemA hymemB hyeqfx

    have hyeqg'z' := Func.app_inv g hgbij y z' hymemB hz'memC hz'eqgy

    have hzeqz' : z =st z' := by
        calc
            z =st Func.app (Func.comp g f) x
                := hzeqgfx

            _ =st Func.app g (Func.app f x)
                := Func.app_comp f g hxmemA

            _ =st Func.app g (Func.app f (Func.app f' y))
                := Func.app_congr_right (
                    Func.app_congr_right hxeqf'y)

            _ =st Func.app g y
                := Func.app_congr_right (
                    Func.canc_bij_ff' f f' hfbij hf'eqfinv y hymemB)

            _ =st Func.app g (Func.app g' z')
                := Func.app_congr_right hyeqg'z'

            _ =st z'
                := Func.canc_bij_ff' g g' hgbij hg'eqginv z' hz'memC

    calc
        Func.app «(gf)'» z
            =st x
                := St.eq_symm «hxeq(gf)'z»

        _   =st Func.app f' y
                := hxeqf'y

        _   =st Func.app f' (Func.app g' z')
                := Func.app_congr_right hyeqg'z'

        _   =st Func.app f' (Func.app g' z)
                := Func.app_congr_right (
                    Func.app_congr_right (
                        St.eq_symm hzeqz'))

        _   =st Func.app (Func.comp f' g') z
                := St.eq_symm (Func.app_comp g' f' hzmemC)


theorem Func.comp_incl_from_incl {A B C : St}
    (hAsubB : St.subset A B) (hBsubC : St.subset B C)
    (hAsubC : St.subset A C := St.subset_trans A B C hAsubB hBsubC) :

    Func.comp (Func.incl B C hBsubC) (Func.incl A B hAsubB) =func
        Func.incl A C  hAsubC := by

    let f := Func.incl A B hAsubB
    let g := Func.incl B C hBsubC
    let h := Func.incl A C hAsubC

    apply (Func.ext (Func.comp g f) h).mp
    intro x hxmemA

    have hxmemB : St.mem x B := (St.mem_subset A B).mp hAsubB x hxmemA

    calc
        Func.app (Func.comp g f) x

            =st Func.app g (Func.app f x)
                := Func.app_comp f g hxmemA

        _   =st Func.app g x
                := Func.app_congr_right (
                    Func.app_incl hAsubB x hxmemA)

        _   =st x
                := Func.app_incl hBsubC x hxmemB

        _   =st Func.app h x
                := St.eq_symm (Func.app_incl hAsubC x hxmemA)

theorem Func.comp_dom_identity {A B : St} (f : Func A B)
    (hAsubA : St.subset A A := St.subset_rfl A) :

    Func.comp f (Func.incl A A hAsubA) =func f := by

    let i := (Func.incl A A hAsubA)

    apply (Func.ext (Func.comp f i) f).mp
    intro x hxmemA

    calc
        Func.app (Func.comp f i) x

            =st Func.app f (Func.app i x)
                := Func.app_comp i f hxmemA

        _   =st Func.app f x
                := Func.app_congr_right (
                    Func.app_incl hAsubA x hxmemA)


theorem Func.comp_codom_identity {A B : St} (f : Func A B)
    (hBsubB : St.subset B B := St.subset_rfl B) :

    Func.comp (Func.incl B B hBsubB) f =func f := by

    let i := (Func.incl B B hBsubB)

    apply (Func.ext (Func.comp i f) f).mp
    intro x hxmemA

    have ⟨y, hymemB, hyeqfx⟩ := Func.tot f x hxmemA

    calc
        Func.app (Func.comp i f) x

        _   =st Func.app i (Func.app f x)
                := Func.app_comp f i hxmemA

        _   =st Func.app i y
                := Func.app_congr_right (St.eq_symm hyeqfx)

        _   =st y
                := Func.app_incl hBsubB y hymemB

        _   =st Func.app f x
                := hyeqfx


theorem Func.dom_identity_from_bij {A B : St}
    (f : Func A B) (hfbij : Func.bij f)
    (hAsubA : St.subset A A := St.subset_rfl A) :

    Func.comp (Func.inv f hfbij) f =func Func.incl A A hAsubA := by

    let f' := Func.inv f hfbij
    have hf'eqfinv : f' =func Func.inv f hfbij := by rfl

    let i := Func.incl A A hAsubA

    apply (Func.ext (Func.comp f' f) i).mp
    intro x hxmemA

    calc
        Func.app (Func.comp f' f) x
            =st Func.app f' (Func.app f x)
                := Func.app_comp f f' hxmemA

        _   =st x
                := Func.canc_bij_f'f f f' hfbij hf'eqfinv x hxmemA

        _   =st Func.app i x
                := St.eq_symm (Func.app_incl hAsubA x hxmemA)


theorem Func.codom_identity_from_bij {A B : St}
    (f : Func A B) (hfbij : Func.bij f)
    (hBsubB : St.subset B B := St.subset_rfl B) :

    Func.comp f (Func.inv f hfbij) =func Func.incl B B hBsubB := by

    let f' := Func.inv f hfbij
    have hf'eqfinv : f' =func Func.inv f hfbij := by rfl

    let i := Func.incl B B hBsubB

    apply (Func.ext (Func.comp f f') i).mp
    intro y hymemB

    calc
        Func.app (Func.comp f f') y
            =st Func.app f (Func.app f' y)
                := Func.app_comp f' f hymemB

        _   =st y
                := Func.canc_bij_ff' f f' hfbij hf'eqfinv y hymemB

        _   =st Func.app i y
                := St.eq_symm (Func.app_incl hBsubB y hymemB)



theorem Func.unique_piecewise_function {A B C : St}
    (hAinterBempty : St.inter A B =st St.empty)
    (f : Func A C) (g : Func B C)
    (hAsubAB : St.subset A (St.uni A B) := St.subset_of_uni_left A B)
    (hBsubAB : St.subset B (St.uni A B) := St.subset_of_uni_right A B) :

    let iA := Func.incl A (St.uni A B) hAsubAB
    let iB := Func.incl B (St.uni A B) hBsubAB
    let piecewise_comps (h : Func (St.uni A B) C) :=
        (Func.comp h iA =func f ∧ Func.comp h iB =func g)

    ∃ h : Func (St.uni A B) C, piecewise_comps h ∧
        ∀ h' : Func (St.uni A B) C, piecewise_comps h' → h' =func h

    := by

    intro iA iB piecewise_comps

    let h := Func.piecewise f g

    have hpiecewise_compsh : piecewise_comps h := by
      constructor
      · apply (Func.ext (Func.comp h iA) f).mp
        intro x hxmemA
        calc
          Func.app (Func.comp h iA) x

              =st Func.app h (Func.app iA x)
                  := Func.app_comp iA h hxmemA

          _   =st Func.app h x
                  := Func.app_congr_right (
                      Func.app_incl hAsubAB x hxmemA)

          _   =st Func.app f x
                  := Func.app_piecewise_left f g x hxmemA

      · apply (Func.ext (Func.comp h iB) g).mp
        intro x hxmemB

        have hxmemAfalse : St.mem x A → False := by
          intro hxmemA
          apply (St.mem_empty x).mp
          rw [St.mem_congr_right (St.eq_symm hAinterBempty)]
          apply (St.mem_inter A B x).mpr
          constructor
          · exact hxmemA
          · exact hxmemB

        calc
          Func.app (Func.comp h iB) x

              =st Func.app h (Func.app iB x)
                  := Func.app_comp iB h hxmemB

          _   =st Func.app h x
                  := Func.app_congr_right (
                      Func.app_incl hBsubAB x hxmemB)

          _   =st Func.app g x
                  := Func.app_piecewise_right f g x hxmemB hxmemAfalse


    exists h


    constructor
    · exact hpiecewise_compsh

    · intro h' hpiecewise_compsh'

      rcases hpiecewise_compsh with ⟨hhiAeqf, hhiBeqg⟩
      rcases hpiecewise_compsh' with ⟨hh'iAeqf, hh'iBeqg⟩

      apply (Func.ext h' h).mp
      intro x hxmemAuniB

      have hxmemAorB : St.mem x A ∨ St.mem x B :=
        (St.mem_uni A B x).mp hxmemAuniB

      rcases hxmemAorB with hxmemA | hxmemB
      · calc
        Func.app h' x
            =st Func.app h' (Func.app iA x)
                := Func.app_congr_right (
                    St.eq_symm (Func.app_incl hAsubAB x hxmemA))

        _   =st Func.app (Func.comp h' iA) x
                := St.eq_symm (Func.app_comp iA h' hxmemA)

        _   =st Func.app f x
                := Func.app_congr_left hh'iAeqf

        _   =st Func.app (Func.comp h iA) x
                := Func.app_congr_left (Func.eq_symm hhiAeqf)

        _   =st Func.app h (Func.app iA x)
                := Func.app_comp iA h hxmemA

        _   =st Func.app h x
                := Func.app_congr_right (
                    Func.app_incl hAsubAB x hxmemA)

      · calc
        Func.app h' x
            =st Func.app h' (Func.app iB x)
                := Func.app_congr_right (
                    St.eq_symm (Func.app_incl hBsubAB x hxmemB))

        _   =st Func.app (Func.comp h' iB) x
                := St.eq_symm (Func.app_comp iB h' hxmemB)

        _   =st Func.app g x
                := Func.app_congr_left hh'iBeqg

        _   =st Func.app (Func.comp h iB) x
                := Func.app_congr_left (Func.eq_symm hhiBeqg)

        _   =st Func.app h (Func.app iB x)
                := Func.app_comp iB h hxmemB

        _   =st Func.app h x
                := Func.app_congr_right (
                    Func.app_incl hBsubAB x hxmemB)

























