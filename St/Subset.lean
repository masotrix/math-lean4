import St.Membership


/- Subset definition -/


axiom subset : St → St → Prop


/- Subset axioms & definitions -/


axiom mem_subset (A B : St) :
    subset A B ↔ ∀ x : St, mem x A → mem x B

def subset_prop (A B : St) : Prop :=
    subset A B ∧ ((A =st B) → False)


/- Subset props -/


theorem subset_trans (A B C : St) :
    subset A B → subset B C → subset A C := by

    rw [mem_subset A B]
    rw [mem_subset B C]
    rw [mem_subset A C]
    intro hAB hBC x hxmemA
    apply (hBC x)
    apply (hAB x)
    exact hxmemA


theorem subset_antisymm (A B : St) :
    subset A B → subset B A → A =st B := by

    rw [mem_subset A B]
    rw [mem_subset B A]
    intro hAB hBA
    apply (set_eq A B).mp
    intro x

    constructor
    · /- mem x A -> mem x B -/
      intro hA
      apply (hAB x)
      exact hA
    · /- mem x B -> mem x A -/
      intro hB
      apply (hBA x)
      exact hB


theorem subset_prop_trans (A B C : St) :
    subset_prop A B → subset_prop B C → subset_prop A C := by

    unfold subset_prop
    intro hAB hBC
    obtain ⟨hAB, hneAB⟩ := hAB
    obtain ⟨hBC, hneBC⟩ := hBC

    constructor
    · /- subset A C -/
      exact (subset_trans A B C hAB hBC)

    · /- A = C -> False -/

      rw [mem_subset A B] at hAB
      rw [mem_subset B C] at hBC

      intro heqAC
      apply hneAB

      apply (set_eq A B).mp

      intro x

      constructor
      · /- mem x A -> mem x B -/
        exact (hAB x)

      · /- mem x B -> mem x A -/
        rw [mem_congr_right heqAC]
        exact (hBC x)

theorem subset_uni_left (A X : St) :
    subset A X → (uni A X =st X) := by

    intro h
    replace h := (mem_subset A X).mp h
    apply (set_eq (uni A X) X).mp
    intro x
    rw [mem_uni]

    constructor
    · intro hAorX
      rcases hAorX with hA | hX
      · have hX := h x hA
        exact hX
      · exact hX
    · intro hX
      right
      exact hX

theorem subset_uni_right (A X : St) :
    subset A X → (uni X A =st X) := by

    intro h
    calc
      uni X A
        =st uni A X := by apply uni_comm
      _ =st X := by apply (subset_uni_left A X h)

theorem subset_then_inter_left (A X : St) :
    subset A X → (inter A X =st A) := by

    intro h
    replace h := (mem_subset A X).mp h
    apply (set_eq (inter A X) A).mp
    intro x
    rw [mem_inter]

    constructor
    · intro hAandX
      obtain ⟨hA, hX⟩ := hAandX
      exact hA
    · intro hA
      constructor
      · exact hA
      · have hX := h x hA
        exact hX

theorem subset_then_inter_right (A X : St) :
    subset A X → (inter X A =st A) := by

    intro h
    calc
        inter X A
            =st inter A X := by apply inter_comm
        _   =st A := by apply (subset_then_inter_left A X h)

theorem subset_then_diff_uni_left (A X : St) :
    subset A X → (uni A (diff X A) =st X) := by

    rw [mem_subset A X]
    intro h
    apply (set_eq (uni A (diff X A)) X).mp
    intro x
    rw [mem_uni]
    rw [mem_diff]

    constructor
    · intro h
      rcases h with hA | hXneA
      · have hX := h x hA
        exact hX
      · obtain ⟨hX, hneA⟩ := hXneA
        exact hX
    · intro hX
      by_cases hA : mem x A
      · left
        exact hA
      · right
        constructor
        · exact hX
        · exact hA

theorem subset_then_diff_uni_right (A X : St) :
    subset A X → (uni (diff X A) A =st X) := by

    intro h
    calc
        uni (diff X A) A
            =st uni A (diff X A) := by apply uni_comm
        _   =st X := by apply (subset_then_diff_uni_left A X h)

theorem subset_then_diff_inter_left (A X : St) :
    subset A X → (inter A (diff X A) =st empty) := by

    rw [mem_subset A X]
    intro h
    apply (set_eq (inter A (diff X A)) empty).mp
    intro x
    rw [mem_inter]
    rw [mem_diff]

    constructor
    · intro h
      obtain ⟨hA, hXneA⟩ := h
      obtain ⟨hX, hneA⟩ := hXneA
      exfalso
      apply hneA
      exact hA

    · intro h
      replace h := (mem_empty x).mp h
      exfalso
      exact h

theorem subset_then_diff_inter_right (A X : St) :
    subset A X → (inter (diff X A) A =st empty) := by

    intro h
    calc
        inter (diff X A) A
            =st inter A (diff X A) := by apply inter_comm
        _   =st empty := by apply (subset_then_diff_inter_left A X h)


theorem subset_demorgan_uni (X A B : St) :
    diff X (uni A B) =st inter (diff X A) (diff X B) := by

    apply (set_eq (diff X (uni A B)) (inter (diff X A) (diff X B))).mp
    intro x

    rw [mem_diff]
    rw [mem_uni]
    rw [mem_inter]
    rw [mem_diff]
    rw [mem_diff]

    constructor
    · intro h
      obtain ⟨hX, hneAorB⟩ := h
      by_cases hA : mem x A
      · exfalso
        apply hneAorB
        left
        exact hA
      · by_cases hB : mem x B
        · exfalso
          apply hneAorB
          right
          exact hB
        · constructor
          · constructor
            · exact hX
            · exact hA
          · constructor
            · exact hX
            · exact hB
    · intro h
      obtain ⟨hXneA, hXneB⟩ := h
      obtain ⟨hX, hneA⟩ := hXneA
      obtain ⟨hX, hneB⟩ := hXneB

      constructor
      · exact hX
      · intro hAorB
        rcases hAorB with hA | hB
        · apply hneA
          exact hA
        · apply hneB
          exact hB

theorem subset_demorgan_inter (X A B : St) :
    diff X (inter A B) =st uni (diff X A) (diff X B) := by

    apply (set_eq (diff X (inter A B)) (uni (diff X A) (diff X B))).mp
    intro x

    rw [mem_diff]
    rw [mem_inter]
    rw [mem_uni]
    rw [mem_diff]
    rw [mem_diff]

    constructor
    · intro h
      obtain ⟨hX, hneAandB⟩ := h
      by_cases hA : mem x A
      · right
        constructor
        · exact hX
        · intro hB
          apply hneAandB
          constructor
          · exact hA
          · exact hB
      · left
        constructor
        · exact hX
        · intro hneA
          apply hA
          exact hneA
    · intro h
      rcases h with hXneA | hXneB
      · obtain ⟨hX, hneA⟩ := hXneA
        constructor
        · exact hX
        · intro hAandB
          obtain ⟨hA, hB⟩ := hAandB
          apply hneA
          exact hA
      · obtain ⟨hX, hneB⟩ := hXneB
        constructor
        · exact hX
        · intro hAandB
          obtain ⟨hA, hB⟩ := hAandB
          apply hneB
          exact hB

theorem subset_congr_left {A B C : St} (h : A =st B) :
  subset A C ↔ subset B C := by

  constructor
  · rw [mem_subset]
    rw [mem_subset]
    intro hsub x hx
    rw [(mem_congr_right h).symm] at hx
    apply hsub x hx

  · rw [mem_subset]
    rw [mem_subset]
    intro hsub x hx
    rw [mem_congr_right h] at hx
    apply hsub x hx

theorem subset_congr_right {A B C : St} (h : B =st C) :
  subset A B ↔ subset A C := by

  constructor
  · rw [mem_subset]
    rw [mem_subset]
    intro hAB x hA
    have hB := hAB x hA
    rw [mem_congr_right h] at hB
    exact hB

  · rw [mem_subset]
    rw [mem_subset]
    intro hAC x hA
    have hC := hAC x hA
    rw [(mem_congr_right h).symm] at hC
    exact hC


/- Subset subproperties -/


theorem uni_then_subset {A B : St} (h : uni A B =st B) :
    subset A B := by

    apply (mem_subset A B).mpr
    intro x

    replace h := (set_eq (uni A B) B).mpr h x
    rw [mem_uni] at h

    intro hA

    have hAorB : mem x A ∨ mem x B := by
        left
        exact hA

    replace h := h.mp hAorB
    exact h

theorem inter_then_subset {A B : St} (h : inter A B =st A) :
    subset A B := by

    apply (mem_subset A B).mpr
    intro x

    replace h := (set_eq (inter A B) A).mpr h x
    rw [mem_inter] at h

    intro hA

    have hAandB := h.mpr hA

    obtain ⟨hA, hB⟩ := hAandB

    exact hB

theorem uni_great_eq_inter_less (A B : St) :
    (uni A B =st B) ↔ (inter A B =st A) := by

    constructor
    · intro hAuniB
      apply (set_eq (inter A B) A).mp

      intro x

      rw [mem_inter A B x]

      replace hAuniB := (set_eq (uni A B) B).mpr hAuniB x
      rw [mem_uni A B x] at hAuniB

      constructor
      · intro hAandB
        obtain ⟨hA, hB⟩ := hAandB
        exact hA
      · intro hA

        have hAorB : mem x A ∨ mem x B := by
            left
            exact hA

        have hB := hAuniB.mp hAorB
        exact ⟨hA, hB⟩

    · intro hAinterB
      apply (set_eq (uni A B) B).mp

      intro x

      rw [mem_uni A B x]

      replace hAinterB := (set_eq (inter A B) A).mpr hAinterB x
      rw [mem_inter A B x] at hAinterB

      constructor
      · intro hAorB
        rcases hAorB with hA | hB
        · have hAandB := hAinterB.mpr hA
          obtain ⟨hA, hB⟩ := hAandB
          exact hB
        · exact hB
      · intro hB
        right
        exact hB

theorem inter_less_subset_left (A B : St) : subset (inter A B) A := by
    apply (mem_subset (inter A B) A).mpr
    intro x

    rw [mem_inter]
    intro hAandB
    obtain ⟨hA, hB⟩ := hAandB
    exact hA


theorem inter_less_subset_right (A B : St) : subset (inter A B) B := by
    rw [subset_congr_left (inter_comm A B)]
    apply inter_less_subset_left

theorem subset_and_subset_eq_subset_inter (A B C : St) :
    subset C A ∧ subset C B ↔ subset C (inter A B) := by

    constructor
    · intro hCAandCB
      obtain ⟨hCA, hCB⟩ := hCAandCB
      replace hCA := (mem_subset C A).mp hCA
      replace hCB := (mem_subset C B).mp hCB
      apply (mem_subset C (inter A B)).mpr
      intro x hC
      apply (mem_inter A B x).mpr
      have hA := hCA x hC
      have hB := hCB x hC
      exact ⟨hA, hB⟩

    · intro hCinterAB
      replace hCinterAB := (mem_subset C (inter A B)).mp hCinterAB

      constructor
      · apply (mem_subset C A).mpr
        intro x hC
        have hAandB := hCinterAB x hC
        replace hAandB := (mem_inter A B x).mp hAandB
        obtain ⟨hA, hB⟩ := hAandB
        exact hA

      · apply (mem_subset C B).mpr
        intro x hC
        have hAandB := hCinterAB x hC
        replace hAandB := (mem_inter A B x).mp hAandB
        obtain ⟨hA, hB⟩ := hAandB
        exact hB


theorem subset_of_uni_left (A B : St) : subset A (uni A B) := by
    apply (mem_subset A (uni A B)).mpr
    intro x hA
    apply (mem_uni A B x).mpr
    left
    exact hA

theorem subset_of_uni_right (A B : St) : subset B (uni A B) := by
    rw [subset_congr_right (uni_comm A B)]
    apply subset_of_uni_left B A


theorem subset_and_subset_eq_subset_uni (A B C : St) :
    subset A C ∧ subset B C ↔ subset (uni A B) C := by

    constructor
    · intro hACandBC
      obtain ⟨hAC, hBC⟩ := hACandBC
      replace hAC := (mem_subset A C).mp hAC
      replace hBC := (mem_subset B C).mp hBC
      apply (mem_subset (uni A B) C).mpr
      intro x hAorB
      replace hAorB := (mem_uni A B x).mp hAorB
      rcases hAorB with hA | hB
      · have hC := hAC x hA
        exact hC
      · have hC := hBC x hB
        exact hC
    · intro huniABC
      constructor
      · apply (mem_subset A C).mpr
        intro x hA
        replace huniABC := (mem_subset (uni A B) C).mp huniABC
        replace huniABC := huniABC x
        have hAorB : mem x (uni A B) := by
          apply (mem_uni A B x).mpr
          left
          exact hA
        have hC := huniABC hAorB
        exact hC
      · apply (mem_subset B C).mpr
        intro x hB
        replace huniABC := (mem_subset (uni A B) C).mp huniABC
        replace huniABC := huniABC x
        have hAorB : mem x (uni A B) := by
          apply (mem_uni A B x).mpr
          right
          exact hB
        have hC := huniABC hAorB
        exact hC


theorem absortion_inter_uni (A B : St) : inter A (uni A B) =st A := by

    apply (set_eq (inter A (uni A B)) A).mp
    intro x
    constructor
    · intro h
      replace h := (mem_inter A (uni A B) x).mp h
      obtain ⟨hA, hAuniB⟩ := h
      exact hA

    · intro hA
      apply (mem_inter A (uni A B) x).mpr
      constructor
      · exact hA
      · apply (mem_uni A B x).mpr
        left
        exact hA

theorem absortion_uni_inter (A B : St) : uni A (inter A B) =st A := by

    apply (set_eq (uni A (inter A B)) A).mp
    intro x
    constructor
    · intro h
      replace h := (mem_uni A (inter A B) x).mp h
      rcases h with hA | hinterAB
      · exact hA
      · replace hinterAB := (mem_inter A B x).mp hinterAB
        obtain ⟨hA, hB⟩ := hinterAB
        exact hA

    · intro hA
      apply (mem_uni A (inter A B) x).mpr
      left
      exact hA

theorem void_intersection_union_diffs (A B X : St) :
    (uni A B =st X) → (inter A B =st empty) →
    (A =st diff X B) ∧ (B =st diff X A) := by

    have h {A B X : St} (huniAB : uni A B =st X)
      (hinterAB : inter A B =st empty) : (A =st diff X B) := by

      replace huniAB := (set_eq (uni A B) X).mpr huniAB
      replace hinterAB := (set_eq (inter A B) empty).mpr hinterAB

      apply (set_eq A (diff X B)).mp
      intro x

      constructor
      · intro hA
        apply (mem_diff X B x).mpr

        constructor
        · have hxuniAB : mem x (uni A B) := by
            apply (mem_uni A B x).mpr
            left
            exact hA
          have hX : mem x X := (huniAB x).mp hxuniAB
          exact hX

        · have hxneinterAB : mem x (inter A B) → False := by
            intro hxinterAB
            apply (mem_empty x).mp
            have hxempty : mem x empty := (hinterAB x).mp hxinterAB
            exact hxempty
          have hneB : mem x B → False := by
            intro hB
            have hxAandB : mem x (inter A B) := by
              apply (mem_inter A B x).mpr
              exact ⟨hA, hB⟩

            apply (hxneinterAB hxAandB)
          exact hneB

      · intro hxdiffXB
        have hXandneB := (mem_diff X B x).mp hxdiffXB
        obtain ⟨hX, hneB⟩ := hXandneB
        replace huniAB := (huniAB x).mpr hX
        have hAorB := (mem_uni A B x).mp huniAB
        rcases hAorB with hA | hB
        · exact hA
        · exfalso
          apply hneB
          exact hB

    intro huniAB hinterAB

    constructor
    · apply (h huniAB hinterAB)
    · have huniBA : uni B A =st X := by
        calc
            uni B A
                =st uni A B := by apply uni_comm
            _   =st X := by apply huniAB
      have hinterBA : inter B A =st empty := by
        calc
            inter B A
                =st inter A B := by apply inter_comm
            _   =st empty := by apply hinterAB
      apply (h huniBA hinterBA)


theorem diff_inter_disjoint (A B : St) :
    inter (diff A B) (inter A B) =st empty := by

    apply (set_eq (inter (diff A B) (inter A B)) empty).mp
    intro x
    constructor
    · intro h
      replace h := (mem_inter (diff A B) (inter A B) x).mp h
      obtain ⟨hdiffAB, hinterAB⟩ := h

      replace hdiffAB := (mem_diff A B x).mp hdiffAB
      obtain ⟨hA, hneB⟩ := hdiffAB

      replace hinterAB := (mem_inter A B x).mp hinterAB
      obtain ⟨hA, hB⟩ := hinterAB

      exfalso
      apply hneB
      exact hB

    · intro hempty
      exfalso
      apply (mem_empty x).mp
      exact hempty


theorem diffs_disjoint (A B : St) :
    inter (diff A B) (diff B A) =st empty := by

    apply (set_eq (inter (diff A B) (diff B A)) empty).mp
    intro x
    constructor
    · intro h
      replace h := (mem_inter (diff A B) (diff B A) x).mp h
      obtain ⟨hdiffAB, hdiffBA⟩ := h

      replace hdiffBA := (mem_diff B A x).mp hdiffBA
      obtain ⟨hB, hneA⟩ := hdiffBA

      replace hdiffAB := (mem_diff A B x).mp hdiffAB
      obtain ⟨hA, hneB⟩ := hdiffAB

      exfalso
      apply hneB
      exact hB

    · intro hempty
      exfalso
      apply (mem_empty x).mp
      exact hempty

theorem diffs_inter_union :
    uni (uni (diff A B) (diff B A)) (inter A B) =st uni A B := by

    apply (set_eq (uni (uni (diff A B) (diff B A)) (inter A B))
        (uni A B)).mp
    intro x

    constructor
    · intro h
      apply (mem_uni A B x).mpr

      replace h :=
        (mem_uni (uni (diff A B) (diff B A)) (inter A B) x).mp h
      rcases h with hdiff | hinter

      · replace hdiff := (mem_uni (diff A B) (diff B A) x).mp hdiff
        rcases hdiff with hdiffAB | hdiffBA
        · replace hdiffAB := (mem_diff A B x).mp hdiffAB
          obtain ⟨hA, hneB⟩ := hdiffAB
          left
          exact hA
        · replace hdiffBA := (mem_diff B A x).mp hdiffBA
          obtain ⟨hB, hneA⟩ := hdiffBA
          right
          exact hB


      · replace hinter := (mem_inter A B x).mp hinter
        obtain ⟨hA, hB⟩ := hinter
        left
        exact hA

    · intro h
      replace h := (mem_uni A B x).mp h
      apply (mem_uni (uni (diff A B) (diff B A)) (inter A B) x).mpr
      rcases h with hA | hB
      · by_cases hB : mem x B
        · right
          apply (mem_inter A B x).mpr
          constructor
          · exact hA
          · exact hB
        · left
          apply (mem_uni (diff A B) (diff B A) x).mpr
          left
          apply (mem_diff A B x).mpr
          constructor
          · exact hA
          · exact hB
      · by_cases hA : mem x A
        · right
          apply (mem_inter A B x).mpr
          constructor
          · exact hA
          · exact hB
        · left
          apply (mem_uni (diff A B) (diff B A) x).mpr
          right
          apply (mem_diff B A x).mpr
          constructor
          · exact hB
          · exact hA


