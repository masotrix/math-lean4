import St.Subset

axiom St.prop_congr {x y : St} {P : St → Prop} (h : x =st y) :
  P x ↔ P y

axiom St.mem_congr_left {x y A : St} (h : x =st y) :
  St.mem x A ↔ St.mem y A


axiom St.set_exists_replacement (A : St) (P : St → St → Prop)
    (h: ∀ x y1 y2 : St, St.mem x A → P x y1 → P x y2 → (y1 =st y2)) :

    ∃ S : St,
        ∀ z : St, St.mem z S ↔ (∃ x : St, St.mem x A ∧ (P x z))


theorem St.set_exists_specification (A : St) (P : St → Prop) :
    ∃ S : St,
        ∀ y : St, St.mem y S ↔ (St.mem y A ∧ (P y)) := by

    let PR (x y : St) : Prop := P x ∧ (y =st x)

    have hSuniq : (∀ x y1 y2 : St,
        St.mem x A → (PR x y1) → (PR x y2) → (y1 =st y2)) := by

        intro x y1 y2 hxA hPy1 hPy2
        obtain ⟨hPx, hy1x⟩ := hPy1
        obtain ⟨hPx, hy2x⟩ := hPy2

        calc
            y1 =st x  := by apply hy1x
            _  =st y2 := by apply (St.eq_symm hy2x)


    obtain ⟨S, hS⟩ := St.set_exists_replacement A PR hSuniq

    exists S

    intro y

    constructor
    · intro hmemyS
      have hexistsx : ∃ (x : St), St.mem x A ∧ PR x y := by
        apply ((hS y).mp hmemyS)

      obtain ⟨x, hx⟩ := hexistsx
      obtain ⟨hxmemA, hPRxy⟩ := hx
      obtain ⟨hPx, hxeqy⟩ := hPRxy

      constructor
      · have hymemA : St.mem y A :=
          (St.mem_congr_left (A := A) hxeqy).mpr hxmemA

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

axiom St.set_regularity (A : St) (h : (A =st St.empty) → False) :
    ∃ (x : St), St.mem x A ∧ (St.inter x A =st St.empty)


theorem St.set_not_self_member (A : St) : St.mem A A → False := by

    intro hAA

    have hsingletAnotEmpty : (St.singlet A =st empty) → False := by

        intro hsingletAempty
        apply (St.mem_empty A).mp
        rw [← (St.mem_congr_right hsingletAempty)]
        apply (St.mem_singlet A A).mpr
        rfl

    have hreg := St.set_regularity (St.singlet A) hsingletAnotEmpty
    obtain ⟨x, hx⟩ := hreg
    obtain ⟨hxmemsingletA, hxintersingletA⟩ := hx
    replace hxmemsingletA :=
        (St.mem_singlet A x).mp hxmemsingletA
    replace hxintersingletA :=
        (St.ext (St.inter x (St.singlet A)) empty).mpr hxintersingletA

    apply (St.mem_empty x).mp
    apply (hxintersingletA x).mp
    apply (St.mem_inter x (St.singlet A) x).mpr
    constructor
    · rw [(St.mem_congr_left hxmemsingletA)]
      rw [(St.mem_congr_right hxmemsingletA)]
      exact hAA
    · apply (St.mem_singlet A x).mpr
      apply hxmemsingletA

theorem St.set_not_both_members (A B : St) :
    (St.mem A B → False) ∨ (St.mem B A → False) := by

    apply Classical.not_not.mp
    intro h

    have hmorgan : St.mem A B ∧ St.mem B A := by
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

    have hpairABnotEmpty : (St.pair A B =st empty) → False := by

        intro hpairABempty
        replace hpairABempty :=
            (St.ext (St.pair A B) empty).mpr hpairABempty
        apply (St.mem_empty A).mp
        apply (hpairABempty A).mp
        apply (St.mem_pair A B A).mpr
        left
        rfl

    have hreg := St.set_regularity (St.pair A B) hpairABnotEmpty

    obtain ⟨hAmemB, hBmemA⟩ := hmorgan
    obtain ⟨x, hx⟩ := hreg
    obtain ⟨hxmempairAB, hxinterpairAB⟩ := hx
    replace hxinterpairAB :=
        (St.ext (St.inter x (St.pair A B)) empty).mpr hxinterpairAB

    replace hxmempairAB := (St.mem_pair A B x).mp hxmempairAB
    rcases hxmempairAB with hxA | hxB
    · 
      apply (St.mem_empty B).mp
      apply (hxinterpairAB B).mp
      apply (St.mem_inter x (St.pair A B) B).mpr
      constructor
      · 
        rw [(St.mem_congr_right hxA)]
        exact hBmemA
      ·
        apply (St.mem_pair A B B).mpr
        right
        rfl
    · 
      apply (St.mem_empty A).mp
      apply (hxinterpairAB A).mp
      apply (St.mem_inter x (St.pair A B) A).mpr
      constructor
      · 
        rw [(St.mem_congr_right hxB)]
        exact hAmemB
      ·
        apply (St.mem_pair A B A).mpr
        left
        rfl


theorem St.set_universal_equivalence :
    (∀ P : St → Prop, ∃ S : St, ∀ y : St, St.mem y S ↔ P y)
    ↔
    (∃ S : St, ∀ y : St, St.mem y S) := by

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

