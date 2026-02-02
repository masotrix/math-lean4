import St.Membership


/- St.subset definition -/


axiom St.subset : St → St → Prop


/- St.subset axioms & definitions -/


axiom St.mem_subset (A B : St) :
    St.subset A B ↔ ∀ x : St, St.mem x A → St.mem x B

def St.subset_prop (A B : St) : Prop :=
    St.subset A B ∧ ((A =st B) → False)


/- St.subset props -/

theorem St.subset_rfl (A : St) :
    St.subset A A := by

    rw [St.mem_subset A A]
    intro x hxmemA
    exact hxmemA

theorem St.subset_trans (A B C : St) :
    St.subset A B → St.subset B C → St.subset A C := by

    rw [St.mem_subset A B]
    rw [St.mem_subset B C]
    rw [St.mem_subset A C]
    intro hAB hBC x hxmemA
    apply (hBC x)
    apply (hAB x)
    exact hxmemA


theorem St.subset_antisymm (A B : St) :
    St.subset A B → St.subset B A → A =st B := by

    rw [St.mem_subset A B]
    rw [St.mem_subset B A]
    intro hAB hBA
    apply (St.ext A B).mp
    intro x

    constructor
    · /- St.mem x A -> St.mem x B -/
      intro hA
      apply (hAB x)
      exact hA
    · /- St.mem x B -> St.mem x A -/
      intro hB
      apply (hBA x)
      exact hB


theorem St.subset_prop_trans (A B C : St) :
    St.subset_prop A B → St.subset_prop B C → St.subset_prop A C := by

    unfold St.subset_prop
    intro hAB hBC
    obtain ⟨hAB, hneAB⟩ := hAB
    obtain ⟨hBC, hneBC⟩ := hBC

    constructor
    · /- St.subset A C -/
      exact (St.subset_trans A B C hAB hBC)

    · /- A = C -> False -/

      rw [St.mem_subset A B] at hAB
      rw [St.mem_subset B C] at hBC

      intro heqAC
      apply hneAB

      apply (St.ext A B).mp

      intro x

      constructor
      · /- St.mem x A -> St.mem x B -/
        exact (hAB x)

      · /- St.mem x B -> St.mem x A -/
        rw [St.mem_congr_right heqAC]
        exact (hBC x)

theorem St.subset_uni_left (A X : St) :
    St.subset A X → (St.uni A X =st X) := by

    intro h
    replace h := (St.mem_subset A X).mp h
    apply (St.ext (St.uni A X) X).mp
    intro x
    rw [St.mem_uni]

    constructor
    · intro hAorX
      rcases hAorX with hA | hX
      · have hX := h x hA
        exact hX
      · exact hX
    · intro hX
      right
      exact hX

theorem St.subset_uni_right (A X : St) :
    St.subset A X → (St.uni X A =st X) := by

    intro h
    calc
      St.uni X A
        =st St.uni A X := by apply St.uni_comm
      _ =st X := by apply (subset_uni_left A X h)

theorem St.subset_then_inter_left (A X : St) :
    St.subset A X → (St.inter A X =st A) := by

    intro h
    replace h := (St.mem_subset A X).mp h
    apply (St.ext (St.inter A X) A).mp
    intro x
    rw [St.mem_inter]

    constructor
    · intro hAandX
      obtain ⟨hA, hX⟩ := hAandX
      exact hA
    · intro hA
      constructor
      · exact hA
      · have hX := h x hA
        exact hX

theorem St.subset_then_inter_right (A X : St) :
    St.subset A X → (St.inter X A =st A) := by

    intro h
    calc
        St.inter X A
            =st St.inter A X := by apply St.inter_comm
        _   =st A := by apply (subset_then_inter_left A X h)

theorem St.subset_then_diff_uni_left (A X : St) :
    St.subset A X → (St.uni A (St.diff X A) =st X) := by

    rw [St.mem_subset A X]
    intro h
    apply (St.ext (St.uni A (St.diff X A)) X).mp
    intro x
    rw [St.mem_uni]
    rw [St.mem_diff]

    constructor
    · intro h
      rcases h with hA | hXneA
      · have hX := h x hA
        exact hX
      · obtain ⟨hX, hneA⟩ := hXneA
        exact hX
    · intro hX
      by_cases hA : St.mem x A
      · left
        exact hA
      · right
        constructor
        · exact hX
        · exact hA

theorem St.subset_then_diff_uni_right (A X : St) :
    St.subset A X → (St.uni (St.diff X A) A =st X) := by

    intro h
    calc
        St.uni (St.diff X A) A
            =st St.uni A (St.diff X A) := by apply St.uni_comm
        _   =st X := by apply (subset_then_diff_uni_left A X h)

theorem St.subset_then_diff_inter_left (A X : St) :
    St.subset A X → (St.inter A (St.diff X A) =st St.empty) := by

    rw [St.mem_subset A X]
    intro h
    apply (St.ext (St.inter A (St.diff X A)) St.empty).mp
    intro x
    rw [St.mem_inter]
    rw [St.mem_diff]

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

theorem St.subset_then_diff_inter_right (A X : St) :
    St.subset A X → (St.inter (St.diff X A) A =st St.empty) := by

    intro h
    calc
        St.inter (St.diff X A) A
            =st St.inter A (St.diff X A) := by apply St.inter_comm
        _   =st St.empty := by apply (subset_then_diff_inter_left A X h)


theorem St.subset_demorgan_uni (X A B : St) :
    St.diff X (St.uni A B) =st St.inter (St.diff X A) (St.diff X B) := by

    apply (St.ext (St.diff X (St.uni A B)) (St.inter (St.diff X A) (St.diff X B))).mp
    intro x

    rw [St.mem_diff]
    rw [St.mem_uni]
    rw [St.mem_inter]
    rw [St.mem_diff]
    rw [St.mem_diff]

    constructor
    · intro h
      obtain ⟨hX, hneAorB⟩ := h
      by_cases hA : St.mem x A
      · exfalso
        apply hneAorB
        left
        exact hA
      · by_cases hB : St.mem x B
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

theorem St.subset_demorgan_inter (X A B : St) :
    St.diff X (St.inter A B) =st
        St.uni (St.diff X A) (St.diff X B) := by

    apply (St.ext (St.diff X (St.inter A B))
        (St.uni (St.diff X A) (St.diff X B))).mp
    intro x

    rw [St.mem_diff]
    rw [St.mem_inter]
    rw [St.mem_uni]
    rw [St.mem_diff]
    rw [St.mem_diff]

    constructor
    · intro h
      obtain ⟨hX, hneAandB⟩ := h
      by_cases hA : St.mem x A
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

theorem St.subset_congr_left {A B C : St} (h : A =st B) :
  St.subset A C ↔ St.subset B C := by

  constructor
  · rw [St.mem_subset]
    rw [St.mem_subset]
    intro hsub x hx
    rw [(St.mem_congr_right h).symm] at hx
    apply hsub x hx

  · rw [St.mem_subset]
    rw [St.mem_subset]
    intro hsub x hx
    rw [St.mem_congr_right h] at hx
    apply hsub x hx

theorem St.subset_congr_right {A B C : St} (h : B =st C) :
  St.subset A B ↔ St.subset A C := by

  constructor
  · rw [St.mem_subset]
    rw [St.mem_subset]
    intro hAB x hA
    have hB := hAB x hA
    rw [St.mem_congr_right h] at hB
    exact hB

  · rw [St.mem_subset]
    rw [St.mem_subset]
    intro hAC x hA
    have hC := hAC x hA
    rw [(St.mem_congr_right h).symm] at hC
    exact hC


/- St.subset subproperties -/


theorem St.uni_then_subset {A B : St} (h : St.uni A B =st B) :
    St.subset A B := by

    apply (St.mem_subset A B).mpr
    intro x

    replace h := (St.ext (St.uni A B) B).mpr h x
    rw [St.mem_uni] at h

    intro hA

    have hAorB : St.mem x A ∨ St.mem x B := by
        left
        exact hA

    replace h := h.mp hAorB
    exact h

theorem St.inter_then_subset {A B : St} (h : St.inter A B =st A) :
    St.subset A B := by

    apply (St.mem_subset A B).mpr
    intro x

    replace h := (St.ext (St.inter A B) A).mpr h x
    rw [St.mem_inter] at h

    intro hA

    have hAandB := h.mpr hA

    obtain ⟨hA, hB⟩ := hAandB

    exact hB

theorem St.uni_great_eq_inter_less (A B : St) :
    (St.uni A B =st B) ↔ (St.inter A B =st A) := by

    constructor
    · intro hAuniB
      apply (St.ext (St.inter A B) A).mp

      intro x

      rw [St.mem_inter A B x]

      replace hAuniB := (St.ext (St.uni A B) B).mpr hAuniB x
      rw [St.mem_uni A B x] at hAuniB

      constructor
      · intro hAandB
        obtain ⟨hA, hB⟩ := hAandB
        exact hA
      · intro hA

        have hAorB : St.mem x A ∨ St.mem x B := by
            left
            exact hA

        have hB := hAuniB.mp hAorB
        exact ⟨hA, hB⟩

    · intro hAinterB
      apply (St.ext (St.uni A B) B).mp

      intro x

      rw [St.mem_uni A B x]

      replace hAinterB := (St.ext (St.inter A B) A).mpr hAinterB x
      rw [St.mem_inter A B x] at hAinterB

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

theorem St.inter_less_subset_left (A B : St) :
    St.subset (St.inter A B) A := by

    apply (St.mem_subset (St.inter A B) A).mpr
    intro x

    rw [St.mem_inter]
    intro hAandB
    obtain ⟨hA, hB⟩ := hAandB
    exact hA


theorem St.inter_less_subset_right (A B : St) :
    St.subset (St.inter A B) B := by

    rw [St.subset_congr_left (St.inter_comm A B)]
    apply inter_less_subset_left

theorem St.subset_and_subSt.set_eq_subset_inter (A B C : St) :
    St.subset C A ∧ St.subset C B ↔ St.subset C (St.inter A B) := by

    constructor
    · intro hCAandCB
      obtain ⟨hCA, hCB⟩ := hCAandCB
      replace hCA := (St.mem_subset C A).mp hCA
      replace hCB := (St.mem_subset C B).mp hCB
      apply (St.mem_subset C (St.inter A B)).mpr
      intro x hC
      apply (St.mem_inter A B x).mpr
      have hA := hCA x hC
      have hB := hCB x hC
      exact ⟨hA, hB⟩

    · intro hCinterAB
      replace hCinterAB := (St.mem_subset C (St.inter A B)).mp hCinterAB

      constructor
      · apply (St.mem_subset C A).mpr
        intro x hC
        have hAandB := hCinterAB x hC
        replace hAandB := (St.mem_inter A B x).mp hAandB
        obtain ⟨hA, hB⟩ := hAandB
        exact hA

      · apply (St.mem_subset C B).mpr
        intro x hC
        have hAandB := hCinterAB x hC
        replace hAandB := (St.mem_inter A B x).mp hAandB
        obtain ⟨hA, hB⟩ := hAandB
        exact hB


theorem St.subset_of_uni_left (A B : St) :
    St.subset A (St.uni A B) := by

    apply (St.mem_subset A (St.uni A B)).mpr
    intro x hA
    apply (St.mem_uni A B x).mpr
    left
    exact hA

theorem St.subset_of_uni_right (A B : St) :
    St.subset B (St.uni A B) := by

    rw [subset_congr_right (St.uni_comm A B)]
    apply subset_of_uni_left B A


theorem St.subset_and_subSt.set_eq_subset_uni (A B C : St) :
    St.subset A C ∧ St.subset B C ↔ St.subset (St.uni A B) C := by

    constructor
    · intro hACandBC
      obtain ⟨hAC, hBC⟩ := hACandBC
      replace hAC := (St.mem_subset A C).mp hAC
      replace hBC := (St.mem_subset B C).mp hBC
      apply (St.mem_subset (St.uni A B) C).mpr
      intro x hAorB
      replace hAorB := (St.mem_uni A B x).mp hAorB
      rcases hAorB with hA | hB
      · have hC := hAC x hA
        exact hC
      · have hC := hBC x hB
        exact hC
    · intro huniABC
      constructor
      · apply (St.mem_subset A C).mpr
        intro x hA
        replace huniABC := (St.mem_subset (St.uni A B) C).mp huniABC
        replace huniABC := huniABC x
        have hAorB : St.mem x (St.uni A B) := by
          apply (St.mem_uni A B x).mpr
          left
          exact hA
        have hC := huniABC hAorB
        exact hC
      · apply (St.mem_subset B C).mpr
        intro x hB
        replace huniABC := (St.mem_subset (St.uni A B) C).mp huniABC
        replace huniABC := huniABC x
        have hAorB : St.mem x (St.uni A B) := by
          apply (St.mem_uni A B x).mpr
          right
          exact hB
        have hC := huniABC hAorB
        exact hC


theorem St.absortion_inter_uni (A B : St) :
    St.inter A (St.uni A B) =st A := by

    apply (St.ext (St.inter A (St.uni A B)) A).mp
    intro x
    constructor
    · intro h
      replace h := (St.mem_inter A (St.uni A B) x).mp h
      obtain ⟨hA, hAuniB⟩ := h
      exact hA

    · intro hA
      apply (St.mem_inter A (St.uni A B) x).mpr
      constructor
      · exact hA
      · apply (St.mem_uni A B x).mpr
        left
        exact hA

theorem St.absortion_uni_inter (A B : St) :
    St.uni A (St.inter A B) =st A := by

    apply (St.ext (St.uni A (St.inter A B)) A).mp
    intro x
    constructor
    · intro h
      replace h := (St.mem_uni A (St.inter A B) x).mp h
      rcases h with hA | hinterAB
      · exact hA
      · replace hinterAB := (St.mem_inter A B x).mp hinterAB
        obtain ⟨hA, hB⟩ := hinterAB
        exact hA

    · intro hA
      apply (St.mem_uni A (St.inter A B) x).mpr
      left
      exact hA

theorem St.void_intersection_union_diffs (A B X : St) :
    (St.uni A B =st X) → (St.inter A B =st St.empty) →
    (A =st St.diff X B) ∧ (B =st St.diff X A) := by

    have h {A B X : St} (huniAB : St.uni A B =st X)
      (hinterAB : St.inter A B =st St.empty) : (A =st St.diff X B) := by

      replace huniAB := (St.ext (St.uni A B) X).mpr huniAB
      replace hinterAB :=
        (St.ext (St.inter A B) St.empty).mpr hinterAB

      apply (St.ext A (St.diff X B)).mp
      intro x

      constructor
      · intro hA
        apply (St.mem_diff X B x).mpr

        constructor
        · have hxuniAB : St.mem x (St.uni A B) := by
            apply (St.mem_uni A B x).mpr
            left
            exact hA
          have hX : St.mem x X := (huniAB x).mp hxuniAB
          exact hX

        · have hxneinterAB : St.mem x (St.inter A B) → False := by
            intro hxinterAB
            apply (mem_empty x).mp
            have hxempty : St.mem x St.empty :=
                (hinterAB x).mp hxinterAB
            exact hxempty
          have hneB : St.mem x B → False := by
            intro hB
            have hxAandB : St.mem x (St.inter A B) := by
              apply (St.mem_inter A B x).mpr
              exact ⟨hA, hB⟩

            apply (hxneinterAB hxAandB)
          exact hneB

      · intro hxdiffXB
        have hXandneB := (St.mem_diff X B x).mp hxdiffXB
        obtain ⟨hX, hneB⟩ := hXandneB
        replace huniAB := (huniAB x).mpr hX
        have hAorB := (St.mem_uni A B x).mp huniAB
        rcases hAorB with hA | hB
        · exact hA
        · exfalso
          apply hneB
          exact hB

    intro huniAB hinterAB

    constructor
    · apply (h huniAB hinterAB)
    · have huniBA : St.uni B A =st X := by
        calc
            St.uni B A
                =st St.uni A B := by apply St.uni_comm
            _   =st X := by apply huniAB
      have hinterBA : St.inter B A =st St.empty := by
        calc
            St.inter B A
                =st St.inter A B := by apply St.inter_comm
            _   =st St.empty := by apply hinterAB
      apply (h huniBA hinterBA)


theorem St.diff_inter_disjoint (A B : St) :
    St.inter (St.diff A B) (St.inter A B) =st St.empty := by

    apply (St.ext (St.inter (St.diff A B) (St.inter A B)) St.empty).mp
    intro x
    constructor
    · intro h
      replace h := (St.mem_inter (St.diff A B) (St.inter A B) x).mp h
      obtain ⟨hdiffAB, hinterAB⟩ := h

      replace hdiffAB := (St.mem_diff A B x).mp hdiffAB
      obtain ⟨hA, hneB⟩ := hdiffAB

      replace hinterAB := (St.mem_inter A B x).mp hinterAB
      obtain ⟨hA, hB⟩ := hinterAB

      exfalso
      apply hneB
      exact hB

    · intro hempty
      exfalso
      apply (mem_empty x).mp
      exact hempty


theorem St.diffs_disjoint (A B : St) :
    St.inter (St.diff A B) (St.diff B A) =st St.empty := by

    apply (St.ext (St.inter (St.diff A B) (St.diff B A)) St.empty).mp
    intro x
    constructor
    · intro h
      replace h := (St.mem_inter (St.diff A B) (St.diff B A) x).mp h
      obtain ⟨hdiffAB, hdiffBA⟩ := h

      replace hdiffBA := (St.mem_diff B A x).mp hdiffBA
      obtain ⟨hB, hneA⟩ := hdiffBA

      replace hdiffAB := (St.mem_diff A B x).mp hdiffAB
      obtain ⟨hA, hneB⟩ := hdiffAB

      exfalso
      apply hneB
      exact hB

    · intro hempty
      exfalso
      apply (mem_empty x).mp
      exact hempty

theorem St.diffs_inter_union :
    St.uni (St.uni (St.diff A B) (St.diff B A))
        (St.inter A B) =st St.uni A B := by

    apply (St.ext (St.uni (St.uni (St.diff A B) (St.diff B A))
            (St.inter A B))
        (St.uni A B)).mp
    intro x

    constructor
    · intro h
      apply (St.mem_uni A B x).mpr

      replace h :=
        (St.mem_uni (St.uni (St.diff A B) (St.diff B A))
            (St.inter A B) x).mp h

      rcases h with hdiff | hinter

      · replace hdiff := (St.mem_uni (St.diff A B)
        (St.diff B A) x).mp hdiff

        rcases hdiff with hdiffAB | hdiffBA
        · replace hdiffAB := (St.mem_diff A B x).mp hdiffAB
          obtain ⟨hA, hneB⟩ := hdiffAB
          left
          exact hA
        · replace hdiffBA := (St.mem_diff B A x).mp hdiffBA
          obtain ⟨hB, hneA⟩ := hdiffBA
          right
          exact hB


      · replace hinter := (St.mem_inter A B x).mp hinter
        obtain ⟨hA, hB⟩ := hinter
        left
        exact hA

    · intro h
      replace h := (St.mem_uni A B x).mp h
      apply (St.mem_uni (St.uni (St.diff A B) (St.diff B A))
        (St.inter A B) x).mpr
      rcases h with hA | hB
      · by_cases hB : St.mem x B
        · right
          apply (St.mem_inter A B x).mpr
          constructor
          · exact hA
          · exact hB
        · left
          apply (St.mem_uni (St.diff A B) (St.diff B A) x).mpr
          left
          apply (St.mem_diff A B x).mpr
          constructor
          · exact hA
          · exact hB
      · by_cases hA : St.mem x A
        · right
          apply (St.mem_inter A B x).mpr
          constructor
          · exact hA
          · exact hB
        · left
          apply (St.mem_uni (St.diff A B) (St.diff B A) x).mpr
          right
          apply (St.mem_diff B A x).mpr
          constructor
          · exact hB
          · exact hA


