import St.Axioms


/- Func definition -/


axiom Func : St → St → Type
axiom Func.eq {A B : St} : Func A B → Func A B → Prop
infix:50 " =func " => Func.eq

axiom Func.app {A B : St} : Func A B → St → St

axiom Func.tot {A B : St} (f : Func A B) :

    ∀ x : St, St.mem x A → ∃ y : St, St.mem y B ∧ (y =st Func.app f x)

axiom Func.from_Rel {A B : St} {P : St → St → Prop}
  (h_tot : ∀ x : St, St.mem x A → ∃ y, St.mem y B ∧ P x y)
  (h_uniq : ∀ x y1 y2 : St, St.mem x A → P x y1 → P x y2 → (y1 =st y2))
  : Func A B

axiom Func.app_congr_right {A B : St} {f : Func A B} {x y : St} :
    (x =st y) → (Func.app f x =st Func.app f y)

axiom Func.app_congr_left {A B : St} {f g : Func A B} {x : St} :
    (f =func g) → (Func.app f x =st Func.app g x)


/- Function creation -/


axiom Func.exists_const {B : St} (A b : St) (h : St.mem b B) :
  ∃ f : Func A B, ∀ x, St.mem x A → Func.app f x =st b

axiom Func.exists_incl {A B : St} (hAsubB : St.subset A B) :
  ∃ f : Func A B, ∀ x, St.mem x A → Func.app f x =st x

axiom Func.exists_piecewise {A B C : St}
    (f : Func A C) (g : Func B C) :

  ∃ h : Func (St.uni A B) C,
    (∀ x, St.mem x A → Func.app h x =st Func.app f x) ∧
    (∀ x, St.mem x B → ¬(St.mem x A) → Func.app h x =st Func.app g x)

axiom Func.exists_congr_dom {A A' B : St}
    (hAeqA' : A =st A') (f : Func A B) :

  ∃ f' : Func A' B, ∀ x, St.mem x A' → Func.app f' x =st Func.app f x


noncomputable def Func.const {B : St} (A b : St)
    (hbmemB : St.mem b B) : Func A B :=

  Classical.choose (Func.exists_const A b hbmemB)

noncomputable def Func.incl (A B : St)
    (hAsubB: St.subset A B) : Func A B :=

  Classical.choose (Func.exists_incl hAsubB)

noncomputable def Func.id (A : St) : Func A A :=

  Classical.choose (Func.exists_incl (St.subset_rfl A))

noncomputable def Func.piecewise {A B C : St}
    (f : Func A C) (g : Func B C) : Func (St.uni A B) C :=

  Classical.choose (Func.exists_piecewise f g)

noncomputable def Func.congr_dom {A A' B : St}
    (hAeqA' : A =st A') (f : Func A B) : Func A' B :=

  Classical.choose (Func.exists_congr_dom hAeqA' f)


theorem Func.app_const {B : St} (A b : St)
  (hbmemB : St.mem b B) :

  ∀ x, St.mem x A → Func.app (Func.const A b hbmemB) x =st b :=

  Classical.choose_spec (Func.exists_const A b hbmemB)


theorem Func.app_incl {A B : St} (hAsubB : St.subset A B) :
  ∀ x, St.mem x A → Func.app (Func.incl A B hAsubB) x =st x :=

  Classical.choose_spec (Func.exists_incl hAsubB)


theorem Func.app_id {A : St} :
  ∀ x, St.mem x A → Func.app (Func.id A) x =st x :=

  Classical.choose_spec (Func.exists_incl (St.subset_rfl A))


theorem Func.app_piecewise_left {A B C : St}
    (f : Func A C) (g : Func B C) :

  ∀ x, St.mem x A → Func.app (Func.piecewise f g) x =st Func.app f x :=

  (Classical.choose_spec (Func.exists_piecewise f g)).1


theorem Func.app_piecewise_right {A B C : St}
    (f : Func A C) (g : Func B C) :

  ∀ x, St.mem x B → ¬(St.mem x A) →
    Func.app (Func.piecewise f g) x =st Func.app g x :=

  (Classical.choose_spec (Func.exists_piecewise f g)).2


theorem Func.app_congr_dom {A : St}
    (hAeqA' : A =st A') (f : Func A B) :

  ∀ x, St.mem x A' → Func.app (Func.congr_dom hAeqA' f) x =st
    Func.app f x :=

  Classical.choose_spec (Func.exists_congr_dom hAeqA' f)


/- Equality -/


axiom Func.ext {A B : St} (f g : Func A B) :
    (∀ x : St, St.mem x A → (Func.app f x =st Func.app g x)) ↔
    f =func g

@[refl]
theorem Func.eq_rfl {A B : St} (f : Func A B) : f =func f := by
    apply (Func.ext f f).mp
    intro x hxmemA
    rfl

theorem Func.eq_symm {A B : St} {f g : Func A B} :
    f =func g → g =func f := by

    intro hfeqg

    have hxfxeqgx := (Func.ext f g).mpr hfeqg

    apply (Func.ext g f).mp

    intro x hxmemA

    apply St.eq_symm (hxfxeqgx x hxmemA)

theorem Func.eq_trans {A B : St} {f g h : Func A B} :
    f =func g → g =func h → f =func h := by

    intro hfeqg hgeqh
    have hxfxeqgx := (Func.ext f g).mpr hfeqg
    have hxgxeqhx := (Func.ext g h).mpr hgeqh

    apply (Func.ext f h).mp

    intro x hxmemA

    apply St.eq_trans (hxfxeqgx x hxmemA) (hxgxeqhx x hxmemA)


/- Composition -/


axiom Func.comp {A B C : St} : (Func B C) → (Func A B) → (Func A C)

axiom Func.app_comp {A B C x : St} (f : Func A B) (g : Func B C) :
    St.mem x A →
        (Func.app (Func.comp g f) x =st Func.app g (Func.app f x))

theorem Func.comp_exists {A B C : St} (f : Func A B) (g : Func B C) :
    ∃ h : Func A C, h =func Func.comp g f := by

    exists (Func.comp g f)

theorem Func.comp_ass {A B C D : St}
    (f : Func A B) (g : Func B C) (h : Func C D) :

    Func.comp h (Func.comp g f) =func Func.comp (Func.comp h g) f := by

    apply (Func.ext (Func.comp h (Func.comp g f))
        (Func.comp (Func.comp h g) f)).mp

    intro x hxmemA

    have ⟨y, hymemB, hyeqfx⟩ := Func.tot f x hxmemA

    calc
        Func.app (Func.comp h (Func.comp g f)) x
            =st  Func.app h (Func.app (Func.comp g f) x)
                := Func.app_comp (Func.comp g f) h hxmemA

        _   =st Func.app h (Func.app g (Func.app f x))
                := Func.app_congr_right (
                    Func.app_comp f g hxmemA)

        _   =st Func.app h (Func.app g y)
                := Func.app_congr_right (
                    Func.app_congr_right (St.eq_symm hyeqfx))

        _   =st Func.app (Func.comp h g) y
                := St.eq_symm (Func.app_comp g h hymemB)

        _   =st Func.app (Func.comp h g) (Func.app f x)
                := Func.app_congr_right hyeqfx

        _   =st Func.app (Func.comp (Func.comp h g) f) x
                := St.eq_symm (
                    Func.app_comp f (Func.comp h g) hxmemA)


theorem Func.comp_congr_left {A B C : St}
    {f : Func A B} {g1 g2 : Func B C} :

    (g1 =func g2) → (Func.comp g1 f =func Func.comp g2 f) := by

    intro hg1eqg2

    apply (Func.ext (Func.comp g1 f) (Func.comp g2 f)).mp

    intro x hxmemA

    calc
        (Func.app (Func.comp g1 f) x)
            =st (Func.app g1 (Func.app f x))
                := (Func.app_comp f g1 hxmemA)

        _   =st Func.app g2 (Func.app f x)
                := Func.app_congr_left hg1eqg2

        _   =st Func.app (Func.comp g2 f) x
                := St.eq_symm (Func.app_comp f g2 hxmemA)


theorem Func.comp_congr_right {A B C : St}
    {f1 f2 : Func A B} {g : Func B C} :

    (f1 =func f2) → (Func.comp g f1 =func Func.comp g f2) := by

    intro hf1eqf2

    apply (Func.ext (Func.comp g f1) (Func.comp g f2)).mp

    intro x hxmemA

    calc
        (Func.app (Func.comp g f1) x)
            =st (Func.app g (Func.app f1 x))
                := (Func.app_comp f1 g hxmemA)

        _   =st Func.app g (Func.app f2 x)
                := Func.app_congr_right (
                    Func.app_congr_left hf1eqf2)

        _   =st Func.app (Func.comp g f2) x
                := St.eq_symm (Func.app_comp f2 g hxmemA)


/- Injection & Onto -/


axiom Func.inj {A B : St} (f : Func A B) : Prop

axiom Func.is_inj {A B : St} (f : Func A B) :
    Func.inj f ↔

    ∀ x x' : St, St.mem x A → St.mem x' A →
        (Func.app f x =st Func.app f x') → x =st x'


theorem Func.comp_inj {A B C : St} (f : Func A B) (g : Func B C) :
    Func.inj f → Func.inj g → Func.inj (Func.comp g f) := by

    intro hinjf hinjg

    replace hinjf := (Func.is_inj f).mp hinjf
    replace hinjg := (Func.is_inj g).mp hinjg

    apply (Func.is_inj (Func.comp g f)).mpr

    intro x x' hxmemA hx'memA hgfxeqgfx'

    have ⟨y, hymemB, hyeqfx⟩ := Func.tot f x hxmemA
    have ⟨y', hy'memB, hy'eqfx'⟩ := Func.tot f x' hx'memA

    have hgyeqgy' : Func.app g y =st Func.app g y' := by
        calc
            Func.app g y
                =st Func.app g (Func.app f x)
                    := Func.app_congr_right hyeqfx
            _   =st Func.app (Func.comp g f) x
                    := St.eq_symm (Func.app_comp f g hxmemA)
            _   =st Func.app (Func.comp g f) x'
                    := hgfxeqgfx'
            _   =st Func.app g (Func.app f x')
                    := Func.app_comp f g hx'memA
            _   =st Func.app g y'
                    := Func.app_congr_right (St.eq_symm hy'eqfx')

    have hyeqy' := hinjg y y' hymemB hy'memB hgyeqgy'

    have hfxeqfx' : Func.app f x =st Func.app f x' := by
        calc
            Func.app f x
                =st y
                    := St.eq_symm hyeqfx
            _   =st y'
                    := hyeqy'
            _   =st Func.app f x'
                    := hy'eqfx'

    have hxeqx' := hinjf x x' hxmemA hx'memA hfxeqfx'

    exact hxeqx'


axiom Func.onto {A B : St} (f : Func A B) : Prop

axiom Func.is_onto {A B : St} (f : Func A B) :
    Func.onto f ↔

    ∀ y : St, St.mem y B → ∃ x : St, St.mem x A ∧ (y =st Func.app f x)

theorem Func.comp_onto {A B C : St} (f : Func A B) (g : Func B C) :
    Func.onto f → Func.onto g → Func.onto (Func.comp g f) := by

    intro hontof hontog

    replace hontof := (Func.is_onto f).mp hontof
    replace hontog := (Func.is_onto g).mp hontog

    apply (Func.is_onto (Func.comp g f)).mpr

    intro z hzmemC

    rcases (hontog z hzmemC) with ⟨y, hymemB, hzeqgy⟩
    rcases (hontof y hymemB) with ⟨x, hxmemA, hyeqfx⟩

    exists x
    constructor
    · exact hxmemA
    · calc
        z
            =st Func.app g y
                := hzeqgy

        _   =st Func.app g (Func.app f x)
                := Func.app_congr_right hyeqfx

        _   =st Func.app (Func.comp g f) x
                := St.eq_symm (Func.app_comp f g hxmemA)


theorem Func.empty_inj {A : St} (f : Func St.empty A) :
    Func.inj f := by

    apply (Func.is_inj f).mpr
    intro x x' hxmemEmp hx'memEmp

    exfalso
    apply (St.mem_empty x).mp
    exact hxmemEmp


theorem Func.canc_comp_left {A B C : St}
    (f f' : Func A B) (g : Func B C) :

    Func.comp g f =func Func.comp g f' → Func.inj g → f =func f' := by

    intro hgfeqgf' hinjg

    apply (Func.ext f f').mp

    intro x hxmemA

    have hgfxeqgf'x :=
        (Func.ext (Func.comp g f) (Func.comp g f')).mpr hgfeqgf'

    replace hgfxeqgf'x := hgfxeqgf'x x hxmemA

    replace hinjg := (Func.is_inj g).mp hinjg

    have ⟨y, hymemB, hyeqfx⟩ := Func.tot f x hxmemA
    have ⟨y', hy'memB, hy'eqf'x⟩ := Func.tot f' x hxmemA

    have hgyeqgy' : Func.app g y =st Func.app g y' := by
        calc
            Func.app g y
                =st Func.app g (Func.app f x)
                    := Func.app_congr_right hyeqfx

            _   =st Func.app (Func.comp g f) x
                    := St.eq_symm (Func.app_comp f g hxmemA)

            _   =st Func.app (Func.comp g f') x
                    := hgfxeqgf'x

            _   =st Func.app g (Func.app f' x)
                    := Func.app_comp f' g hxmemA

            _   =st Func.app g y'
                    := St.eq_symm (Func.app_congr_right hy'eqf'x)


    have hyeqy' := hinjg y y' hymemB hy'memB hgyeqgy'

    have hfxeqf'x : Func.app f x =st Func.app f' x := by
        calc
            Func.app f x
            _   =st y
                := St.eq_symm hyeqfx

            _   =st y'
                := hyeqy'

            _   =st Func.app f' x
                := hy'eqf'x

    exact hfxeqf'x

--   ∀ x x' : St, St.mem x A → St.mem x' A →
--      (Func.app f x =st Func.app f x') → x =st x'

theorem Func.no_canc_comp_left :

    ∃ A B C : St, ∃ f f' : Func A B, ∃ g : Func B C,

        (f =func f' → False) ∧
        (Func.comp g f =func Func.comp g f') := by

    let A := (St.pair St.empty (St.singlet St.empty))
    let B := A
    let C := B

    exists A, B, C

    have hzeromemA : St.mem St.empty A := by
        apply (St.mem_pair St.empty (St.singlet St.empty) St.empty).mpr
        left
        rfl

    have honememA : St.mem (St.singlet St.empty) A := by
        apply (St.mem_pair St.empty (St.singlet St.empty)
            (St.singlet St.empty)).mpr
        right
        rfl

    have hzeromemB := hzeromemA
    have honememB := honememA
    have hzeromemC := hzeromemB

    let f : Func A B := Func.const A St.empty hzeromemB
    let f' : Func A B := Func.const A (St.singlet St.empty) honememB

    exists f, f'


    let g : Func B C := Func.const B St.empty hzeromemC

    exists g

    constructor
    ·   intro hfeqf'
        have hzeroeqone : St.empty =st St.singlet St.empty := by
            --intro x hxmemA
            calc
                St.empty
                    =st Func.app f St.empty
                        := St.eq_symm (Func.app_const A
                            St.empty hzeromemB
                            St.empty hzeromemA)

                _   =st Func.app f' St.empty
                        := (Func.ext f f').mpr hfeqf' St.empty hzeromemA

                _   =st St.singlet St.empty
                        := Func.app_const A
                            (St.singlet St.empty) honememB
                            St.empty hzeromemA 

        have hzeromemzero : St.mem St.empty St.empty := by
            rw [(St.mem_congr_right hzeroeqone)]
            apply (St.mem_singlet St.empty St.empty).mpr
            rfl

        apply (St.mem_empty St.empty).mp hzeromemzero

    ·
        apply (Func.ext (Func.comp g f) (Func.comp g f')).mp

        intro x hxmemA

        have hxeqzeroorxeqone :
            (x =st St.empty) ∨ (x =st (St.singlet St.empty)) := by

            apply (St.mem_pair St.empty
                (St.singlet St.empty) x).mp hxmemA

        rcases hxeqzeroorxeqone with hxeqzero | hxeqone
        · -- app (comp g f) x = app (comp g f') x
          calc
            Func.app (Func.comp g f) x
                =st Func.app (Func.comp g f) St.empty
                    := Func.app_congr_right hxeqzero

            _   =st Func.app g (Func.app f St.empty)
                    := Func.app_comp f g hzeromemA

            _   =st Func.app g St.empty
                    := Func.app_congr_right (
                        Func.app_const A
                            St.empty hzeromemB St.empty hzeromemA)

            _   =st St.empty
                    := Func.app_const B
                        St.empty hzeromemC St.empty hzeromemB

            _   =st Func.app g (St.singlet St.empty)
                    := St.eq_symm (Func.app_const B
                        St.empty hzeromemC
                        (St.singlet St.empty) honememB)

            _   =st Func.app g (Func.app f' St.empty)
                    := Func.app_congr_right (St.eq_symm (
                        Func.app_const A
                            (St.singlet St.empty) honememB
                            St.empty hzeromemA))

            _   =st Func.app (Func.comp g f') St.empty
                    := St.eq_symm (Func.app_comp f' g hzeromemA)

            _   =st Func.app (Func.comp g f') x
                    := Func.app_congr_right (St.eq_symm hxeqzero)

        · -- app (comp g f) zero = app (comp g f') zero
          calc
            Func.app (Func.comp g f) x
                =st Func.app (Func.comp g f) (St.singlet St.empty)
                    := Func.app_congr_right hxeqone

            _   =st Func.app g (Func.app f (St.singlet St.empty))
                    := Func.app_comp f g honememA

            _   =st Func.app g St.empty
                    := Func.app_congr_right (
                        Func.app_const A
                            St.empty hzeromemB
                            (St.singlet St.empty) honememA)

            _   =st St.empty
                    := Func.app_const B
                        St.empty hzeromemC St.empty hzeromemB

            _   =st Func.app g (St.singlet St.empty)
                    := St.eq_symm (Func.app_const B
                        St.empty hzeromemC
                        (St.singlet St.empty) honememB)

            _   =st Func.app g (Func.app f' (St.singlet St.empty))
                    := Func.app_congr_right (St.eq_symm (
                        Func.app_const A
                            (St.singlet St.empty) honememB
                            (St.singlet St.empty) honememA))

            _   =st Func.app (Func.comp g f') (St.singlet St.empty)
                    := St.eq_symm (Func.app_comp f' g honememA)

            _   =st Func.app (Func.comp g f') x
                    := Func.app_congr_right (St.eq_symm hxeqone)


theorem Func.canc_comp_right {A B C : St}
    (f : Func A B) (g g' : Func B C) :

    Func.comp g f =func Func.comp g' f → Func.onto f → g =func g' := by

    intro hgfeqg'f hontof

    apply (Func.ext g g').mp

    intro y hymemB

    replace hontof := (Func.is_onto f).mp hontof
    replace hontof := hontof y hymemB

    have ⟨x, hxmemA, hyeqfx⟩ := hontof

    have hgfxeqg'fx :=
        (Func.ext (Func.comp g f) (Func.comp g' f)).mpr hgfeqg'f

    replace hgfxeqg'fx := hgfxeqg'fx x hxmemA

    have ⟨z, hzmemC, hzeqgy⟩ := Func.tot g y hymemB
    have ⟨z', hz'memC, hz'eqg'y⟩ := Func.tot g' y hymemB

    have hgyeqg'y : Func.app g y =st Func.app g' y := by
        calc
            Func.app g y
                =st Func.app g (Func.app f x)
                    := Func.app_congr_right hyeqfx

            _   =st Func.app (Func.comp g f) x
                    := St.eq_symm (Func.app_comp f g hxmemA)

            _   =st Func.app (Func.comp g' f) x
                    := hgfxeqg'fx

            _   =st Func.app g' (Func.app f x)
                    := Func.app_comp f g' hxmemA

            _   =st Func.app g' y
                    := St.eq_symm (Func.app_congr_right hyeqfx)

    exact hgyeqg'y

theorem Func.no_canc_comp_right :

    ∃ A B C : St, ∃ f : Func A B, ∃ g g' : Func B C,

        (g =func g' → False) ∧
        (Func.comp g f =func Func.comp g' f) := by

    let A := (St.pair St.empty (St.singlet St.empty))
    let B := A
    let C := B
    let B1 := St.singlet St.empty
    let B2 := St.singlet (St.singlet St.empty)

    have hb1b2eqb : St.uni B1 B2 =st B := by
        apply (St.ext (St.uni B1 B2) B).mp
        intro x
        constructor
        · intro hxmemB1B2
          have hxmemB1orxmemB2 := (St.mem_uni B1 B2 x).mp hxmemB1B2
          rcases hxmemB1orxmemB2 with hxmemB1 | hxmemB2
          · have hxeqempty := (St.mem_singlet St.empty x).mp hxmemB1
            apply (St.mem_pair St.empty (St.singlet St.empty) x).mpr
            left
            exact hxeqempty
          · have hxeqone :=
                (St.mem_singlet (St.singlet St.empty) x).mp hxmemB2
            apply (St.mem_pair St.empty (St.singlet St.empty) x).mpr
            right
            exact hxeqone
        · intro hxmemB
          have hxeqzeroorxeqone :=
            (St.mem_pair St.empty (St.singlet St.empty) x).mp hxmemB

          apply (St.mem_uni B1 B2 x).mpr
          rcases hxeqzeroorxeqone with hxeqzero | hxeqone
          · left
            apply (St.mem_singlet St.empty x).mpr
            exact hxeqzero
          · right
            apply (St.mem_singlet (St.singlet St.empty) x).mpr
            exact hxeqone


    exists A, B, C

    have hzeromemB1 : St.mem St.empty B1 := by
        apply (St.mem_singlet St.empty St.empty).mpr
        rfl

    have honememB1false : St.mem (St.singlet St.empty) B1 → False := by
        intro honememB1
        have honeeqzero : St.singlet St.empty =st St.empty :=
            (St.mem_singlet St.empty (St.singlet St.empty)).mp honememB1

        have hzeromemzero : St.mem St.empty St.empty := by
            rw [St.mem_congr_right (St.eq_symm honeeqzero)]
            apply (St.mem_singlet St.empty St.empty).mpr
            rfl

        apply (St.mem_empty St.empty).mp hzeromemzero

    have honememB2 : St.mem (St.singlet St.empty) B2 := by
        apply (St.mem_singlet
            (St.singlet St.empty) (St.singlet St.empty)).mpr
        rfl

    have hzeromemA : St.mem St.empty A := by
        apply (St.mem_pair St.empty (St.singlet St.empty) St.empty).mpr
        left
        rfl

    have honememA : St.mem (St.singlet St.empty) A := by
        apply (St.mem_pair St.empty (St.singlet St.empty)
            (St.singlet St.empty)).mpr
        right
        rfl

    have hzeromemB := hzeromemA
    have honememB := honememA
    have hzeromemC := hzeromemB
    have honememC := honememB

    let f : Func A B := Func.const A St.empty hzeromemB

    exists f


    let g : Func B C := Func.const B St.empty hzeromemC
    let h1 : Func B1 C := Func.const B1 St.empty hzeromemC
    let h2 : Func B2 C := Func.const B2 (St.singlet St.empty) honememC
    let h : Func (St.uni B1 B2) C := Func.piecewise h1 h2
    let g' : Func B C := Func.congr_dom hb1b2eqb h

    exists g, g'


    constructor
    ·   intro hgeqg'
        have hzeroeqone : St.empty =st St.singlet St.empty := by
            calc
                St.empty
                    =st Func.app g (St.singlet St.empty)
                        := St.eq_symm (Func.app_const B
                            St.empty hzeromemC
                            (St.singlet St.empty) honememB)

                _   =st Func.app g' (St.singlet St.empty)
                        := (Func.ext g g').mpr hgeqg'
                            (St.singlet St.empty) honememB

                _   =st Func.app h (St.singlet St.empty)
                        := Func.app_congr_dom
                            hb1b2eqb h

                            (St.singlet St.empty) honememB


                _   =st Func.app h2 (St.singlet St.empty)
                        := Func.app_piecewise_right h1 h2

                            (St.singlet St.empty) honememB2
                            honememB1false

                _   =st St.singlet St.empty
                        := Func.app_const B2
                            (St.singlet St.empty) honememC
                            (St.singlet St.empty) honememB2

        have hzeromemzero : St.mem St.empty St.empty := by
            rw [(St.mem_congr_right hzeroeqone)]
            apply (St.mem_singlet St.empty St.empty).mpr
            rfl

        apply (St.mem_empty St.empty).mp hzeromemzero

    ·
        apply (Func.ext (Func.comp g f) (Func.comp g' f)).mp

        intro x hxmemA

        have hxeqzeroorxeqone :
            (x =st St.empty) ∨ (x =st (St.singlet St.empty)) := by

            apply (St.mem_pair St.empty
                (St.singlet St.empty) x).mp hxmemA

        rcases hxeqzeroorxeqone with hxeqzero | hxeqone
        · -- app (comp g f) x = app (comp g' f) x
          calc
            Func.app (Func.comp g f) x
                =st Func.app (Func.comp g f) St.empty
                    := Func.app_congr_right hxeqzero

            _   =st Func.app g (Func.app f St.empty)
                    := Func.app_comp f g hzeromemA

            _   =st Func.app g St.empty
                    := Func.app_congr_right (
                        Func.app_const A
                            St.empty hzeromemB St.empty hzeromemA)

            _   =st St.empty
                    := Func.app_const B
                        St.empty hzeromemC St.empty hzeromemB

            _   =st Func.app h1 St.empty
                    := St.eq_symm (Func.app_const B1
                        St.empty hzeromemC
                        St.empty hzeromemB1)

            _   =st Func.app h St.empty
                    := St.eq_symm (
                        Func.app_piecewise_left h1 h2
                            St.empty hzeromemB1)

            _   =st Func.app g' St.empty
                    := St.eq_symm (Func.app_congr_dom hb1b2eqb h
                        St.empty hzeromemB)

            --_   =st Func.app (Func.comp g' f) St.empty

            _   =st Func.app g' (Func.app f St.empty)
                    := Func.app_congr_right (St.eq_symm (
                        Func.app_const A
                            St.empty hzeromemB
                            St.empty hzeromemA))

            _   =st Func.app (Func.comp g' f) St.empty
                    := St.eq_symm (Func.app_comp f g' hzeromemA)

            _   =st Func.app (Func.comp g' f) x
                    := Func.app_congr_right (St.eq_symm hxeqzero)

        · -- app (comp g f) one = app (comp g' f) one
          calc
            Func.app (Func.comp g f) x
                =st Func.app (Func.comp g f) (St.singlet St.empty)
                    := Func.app_congr_right hxeqone

            _   =st Func.app g (Func.app f (St.singlet St.empty))
                    := Func.app_comp f g honememA

            _   =st Func.app g St.empty
                    := Func.app_congr_right (
                        Func.app_const A
                            St.empty hzeromemB
                            (St.singlet St.empty) honememA)

            _   =st St.empty
                    := Func.app_const B
                        St.empty hzeromemC St.empty hzeromemB

            _   =st Func.app h1 St.empty
                    := St.eq_symm (Func.app_const B1
                        St.empty hzeromemC
                        St.empty hzeromemB1)

            _   =st Func.app h St.empty
                    := St.eq_symm (
                        Func.app_piecewise_left h1 h2
                            St.empty hzeromemB1)

            _   =st Func.app g' St.empty
                    := St.eq_symm (Func.app_congr_dom hb1b2eqb h
                        St.empty hzeromemB)

            _   =st Func.app g' (Func.app f (St.singlet St.empty))
                    := Func.app_congr_right (St.eq_symm (
                        Func.app_const A
                            St.empty hzeromemB
                            (St.singlet St.empty) honememA))

            _   =st Func.app (Func.comp g' f) (St.singlet St.empty)
                    := St.eq_symm (Func.app_comp f g' honememA)

            _   =st Func.app (Func.comp g' f) x
                    := Func.app_congr_right (St.eq_symm hxeqone)



theorem comp_inj_then_f_inj
    (hgfinj : Func.inj (Func.comp g f)) :

    Func.inj f := by

    apply (Func.is_inj f).mpr

    intro x x' hxmemA hx'memA hfxeqfx'

    have hgfxeqgfx' :
        Func.app (Func.comp g f) x =st Func.app (Func.comp g f) x' := by

        calc
            Func.app (Func.comp g f) x
                =st Func.app g (Func.app f x)
                    := Func.app_comp f g hxmemA 

            _   =st Func.app g (Func.app f x')
                    := Func.app_congr_right hfxeqfx'

            _   =st Func.app (Func.comp g f) x'
                    := St.eq_symm (Func.app_comp f g hx'memA)

    apply (Func.is_inj (Func.comp g f)).mp hgfinj
        x x' hxmemA hx'memA hgfxeqgfx'


theorem Func.comp_inj_no_g_inj :

    ∃ A B C : St, ∃ f : Func A B, ∃ g : Func B C,

        Func.inj (Func.comp g f) ∧ (Func.inj g → False) := by

    let A := St.singlet St.empty
    let B := St.pair St.empty (St.singlet St.empty)
    let C := A

    have hzeromemA : St.mem St.empty A := by
        apply (St.mem_singlet St.empty St.empty).mpr
        rfl

    have hzeromemB : St.mem St.empty B := by
        apply (St.mem_pair St.empty (St.singlet St.empty) St.empty).mpr
        left
        rfl

    have honememB : St.mem (St.singlet St.empty) B := by
        apply (St.mem_pair St.empty (St.singlet St.empty)
            (St.singlet St.empty)).mpr
        right
        rfl

    have hzeromemC := hzeromemA

    let f := Func.const A St.empty hzeromemB
    let g := Func.const B St.empty hzeromemC


    exists A, B, C, f, g

    constructor
    · apply (Func.is_inj (Func.comp g f)).mpr
      intro x x' hxmemA hx'memA hgfxeqgfx'

      have hx'eqzero : x' =st St.empty := by
        apply (St.mem_singlet St.empty x').mp hx'memA

      have hxeqzero : x =st St.empty := by
        apply (St.mem_singlet St.empty x).mp hxmemA

      calc
        x =st St.empty := hxeqzero
        _ =st x' := St.eq_symm hx'eqzero

    · intro hginj
      have hzeroeqone : St.empty =st St.singlet St.empty := by

        apply (Func.is_inj g).mp hginj St.empty (St.singlet St.empty)
            hzeromemB honememB

        calc
            Func.app g St.empty
                =st St.empty
                    := Func.app_const B
                        St.empty hzeromemC
                        St.empty hzeromemB

            _   =st Func.app g (St.singlet St.empty)
                    := St.eq_symm (
                        Func.app_const B
                            St.empty hzeromemC
                            (St.singlet St.empty) honememB)

      have hzeromemzero : St.mem St.empty St.empty := by
        rw [St.mem_congr_right hzeroeqone]
        apply (St.mem_singlet St.empty St.empty).mpr
        rfl

      apply (St.mem_empty St.empty).mp hzeromemzero

theorem comp_onto_then_g_onto
    (hgfonto : Func.onto (Func.comp g f)) :

    Func.onto g := by

    apply (Func.is_onto g).mpr

    intro z hzmemC

    replace hgfonto := (Func.is_onto (Func.comp g f)).mp hgfonto
    rcases (hgfonto z hzmemC) with ⟨x, hxmemA, hzeqgfx⟩
    have ⟨y, hymemB, hyeqfx⟩ := Func.tot f x hxmemA

    exists y

    constructor
    · exact hymemB
    · calc
        z =st Func.app (Func.comp g f) x
            := hzeqgfx

        _ =st Func.app g (Func.app f x)
            := Func.app_comp f g hxmemA

        _ =st Func.app g y
            := Func.app_congr_right (St.eq_symm hyeqfx)

theorem Func.comp_onto_no_f_onto :

    ∃ A B C : St, ∃ f : Func A B, ∃ g : Func B C,

        Func.onto (Func.comp g f) ∧ (Func.onto f → False) := by


    let A := St.singlet St.empty
    let B := St.pair St.empty (St.singlet St.empty)
    let C := A

    have hzeromemA : St.mem St.empty A := by
        apply (St.mem_singlet St.empty St.empty).mpr
        rfl

    have hzeromemB : St.mem St.empty B := by
        apply (St.mem_pair St.empty (St.singlet St.empty) St.empty).mpr
        left
        rfl

    have honememB : St.mem (St.singlet St.empty) B := by
        apply (St.mem_pair St.empty (St.singlet St.empty)
            (St.singlet St.empty)).mpr
        right
        rfl

    have hzeromemC := hzeromemA

    let f := Func.const A St.empty hzeromemB
    let g := Func.const B St.empty hzeromemC

    exists A, B, C, f, g

    constructor
    · apply (Func.is_onto (Func.comp g f)).mpr
      intro z hzmemC

      exists St.empty
      constructor
      · exact hzeromemA
      · have hzeqzero : z =st St.empty := by
            apply (St.mem_singlet St.empty z).mp hzmemC

        calc
            z =st St.empty
                := hzeqzero

            _ =st Func.app g St.empty
                := St.eq_symm (
                    Func.app_const B
                        St.empty hzeromemC
                        St.empty hzeromemB)

            _ =st Func.app g (Func.app f St.empty)
                := Func.app_congr_right (
                    St.eq_symm (
                        Func.app_const A
                            St.empty hzeromemB
                            St.empty hzeromemA))

            _ =st Func.app (Func.comp g f) St.empty
                := St.eq_symm (
                    Func.app_comp f g hzeromemA)


    · intro hfonto

      replace hfonto := (Func.is_onto f).mp hfonto
      rcases (hfonto (St.singlet St.empty) honememB)
        with ⟨x, hxmemA, honeeqfx⟩

      have hxeqzero : x =st St.empty := by
        apply (St.mem_singlet St.empty x).mp hxmemA

      have hzeroeqone : St.empty =st St.singlet St.empty := by
        calc
            St.empty
                =st Func.app f St.empty
                    := St.eq_symm (
                        Func.app_const A
                            St.empty hzeromemB
                            St.empty hzeromemA)

            _   =st Func.app f x
                    := Func.app_congr_right (St.eq_symm hxeqzero)

            _   =st St.singlet St.empty
                    := St.eq_symm honeeqfx

      have hzeromemzero : St.mem St.empty St.empty := by
        rw [St.mem_congr_right hzeroeqone]
        apply (St.mem_singlet St.empty St.empty).mpr
        rfl

      apply (St.mem_empty St.empty).mp
      exact hzeromemzero




/-
    have hfinj : Func.inj f := by
        apply (Func.is_inj f).mpr
        intro x x' hxmemA hx'memA hfxeqfx'

        calc
            x =st Func.app f x
                := St.eq_symm (Func.app_id x hxmemA)

            _ =st Func.app f x'
                := hfxeqfx'

            _ =st x'
                := Funx.app_id x' hx'memA


-/

















