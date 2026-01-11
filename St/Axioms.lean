import St.Subset

axiom prop_congr {x y : St} {P : St → Prop} (h : x =st y) :
  P x ↔ P y

axiom mem_congr_left {x y A : St} (h : x =st y) :
  mem x A ↔ mem y A


axiom set_exists_replacement (A : St) (P : St → St → Prop)
    (h: ∀ x y1 y2 : St, mem x A → P x y1 → P x y2 → (y1 =st y2)) :

    ∃ S : St,
        ∀ z : St, mem z S ↔ (∃ x : St, mem x A ∧ (P x z))


theorem set_exists_specification (A : St) (P : St → Prop) :
    ∃ S : St,
        ∀ y : St, mem y S ↔ (mem y A ∧ (P y)) := by

    let PR (x y : St) : Prop := P x ∧ (y =st x)

    have hSuniq : (∀ x y1 y2 : St,
        mem x A → (PR x y1) → (PR x y2) → (y1 =st y2)) := by

        intro x y1 y2 hxA hPy1 hPy2
        obtain ⟨hPx, hy1x⟩ := hPy1
        obtain ⟨hPx, hy2x⟩ := hPy2

        calc
            y1 =st x  := by apply hy1x
            _  =st y2 := by apply (eqst_symm hy2x)


    obtain ⟨S, hS⟩ := set_exists_replacement A PR hSuniq

    exists S

    intro y

    constructor
    · intro hmemyS
      have hexistsx : ∃ (x : St), mem x A ∧ PR x y := by
        apply ((hS y).mp hmemyS)

      obtain ⟨x, hx⟩ := hexistsx
      obtain ⟨hxmemA, hPRxy⟩ := hx
      obtain ⟨hPx, hxeqy⟩ := hPRxy

      constructor
      · have hymemA : mem y A :=
          (mem_congr_left (A := A) hxeqy).mpr hxmemA

        exact hymemA

      · apply (prop_congr hxeqy).mpr hPx

    · intro hymemAandPy

      apply (hS y).mpr
      exists y
      obtain ⟨hymemA, hPy⟩ := hymemAandPy

      constructor
      · exact hymemA
      · constructor
        · exact hPy
        · rfl

axiom set_regularity (A : St) (h : (A =st empty) → False) :
    ∃ (x : St), mem x A ∧ (inter x A =st empty)


theorem set_not_self_member (A : St) : mem A A → False := by

    intro hAA

    have hsingletAnotEmpty : (singlet A =st empty) → False := by

        intro hsingletAempty
        apply (mem_empty A).mp
        rw [← (mem_congr_right hsingletAempty)]
        apply (mem_singlet A A).mpr
        rfl

    have hreg := set_regularity (singlet A) hsingletAnotEmpty
    obtain ⟨x, hx⟩ := hreg
    obtain ⟨hxmemsingletA, hxintersingletA⟩ := hx
    replace hxmemsingletA :=
        (mem_singlet A x).mp hxmemsingletA
    replace hxintersingletA :=
        (set_eq (inter x (singlet A)) empty).mpr hxintersingletA

    apply (mem_empty x).mp
    apply (hxintersingletA x).mp
    apply (mem_inter x (singlet A) x).mpr
    constructor
    · rw [(mem_congr_left hxmemsingletA)]
      rw [(mem_congr_right hxmemsingletA)]
      exact hAA
    · apply (mem_singlet A x).mpr
      apply hxmemsingletA

theorem set_not_both_members (A B : St) :
    (mem A B → False) ∨ (mem B A → False) := by

    apply Classical.not_not.mp
    intro h

    have hmorgan : mem A B ∧ mem B A := by
        constructor
        · apply Classical.not_not.mp
          intro hAB
          apply h
          left
          intro hleft
          apply hAB
          exact hleft
        · apply Classical.not_not.mp
          intro hBA
          apply h
          right
          intro hright
          apply hBA
          exact hright

    have hpairABnotEmpty : (pair A B =st empty) → False := by

        intro hpairABempty
        replace hpairABempty :=
            (set_eq (pair A B) empty).mpr hpairABempty
        apply (mem_empty A).mp
        apply (hpairABempty A).mp
        apply (mem_pair A B A).mpr
        left
        rfl

    have hreg := set_regularity (pair A B) hpairABnotEmpty

    obtain ⟨hAmemB, hBmemA⟩ := hmorgan
    obtain ⟨x, hx⟩ := hreg
    obtain ⟨hxmempairAB, hxinterpairAB⟩ := hx
    replace hxinterpairAB :=
        (set_eq (inter x (pair A B)) empty).mpr hxinterpairAB

    replace hxmempairAB := (mem_pair A B x).mp hxmempairAB
    rcases hxmempairAB with hxA | hxB
    · 
      apply (mem_empty B).mp
      apply (hxinterpairAB B).mp
      apply (mem_inter x (pair A B) B).mpr
      constructor
      · 
        rw [(mem_congr_right hxA)]
        exact hBmemA
      ·
        apply (mem_pair A B B).mpr
        right
        rfl
    · 
      apply (mem_empty A).mp
      apply (hxinterpairAB A).mp
      apply (mem_inter x (pair A B) A).mpr
      constructor
      · 
        rw [(mem_congr_right hxB)]
        exact hAmemB
      ·
        apply (mem_pair A B A).mpr
        left
        rfl


theorem set_universal_equivalence :
    (∀ P : St → Prop, ∃ S : St, ∀ y : St, mem y S ↔ P y)
    ↔
    (∃ S : St, ∀ y : St, mem y S) := by

    constructor
    · 
      intro huniversalSpec
      let P (y : St) : Prop := y =st y
      obtain ⟨S, hS⟩ := huniversalSpec P
      exists S
      intro y
      apply (hS y).mpr
      rfl
    · 
      intro huniversalSet
      obtain ⟨S, hS⟩ := huniversalSet
      intro P
      have hspec := set_exists_specification S P
      obtain ⟨A, hA⟩ := hspec
      exists A
      intro y
      constructor
      · 
        intro hymemA
        obtain ⟨hymemS, hPy⟩ := (hA y).mp hymemA
        apply hPy
      ·
        intro hPy
        apply (hA y).mpr
        constructor
        · exact (hS y)
        · exact hPy

