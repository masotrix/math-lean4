/- St definition -/


axiom St : Type


/- Membership definition -/


axiom St.mem : St → St → Prop
axiom St.eq : St → St → Prop
infix:50 " =st " => St.eq


/- St properties -/


axiom St.ext (A B : St) :
    (∀ x : St, St.mem x A ↔ St.mem x B) ↔ A =st B

axiom St.exists_general_uni (A : St) :
    ∃ S : St, ∀ x : St, St.mem x S ↔ ∃ y : St, St.mem y A ∧ St.mem x y

axiom St.exists_pair (a b : St) :
    ∃ S : St, ∀ x : St, St.mem x S ↔ ((x =st a) ∨ (x =st b))

axiom St.exists_pow (A : St) :
    ∃ S : St, ∀ x : St, St.mem x S ↔ ∀ y : St, St.mem y x → St.mem y A

axiom St.exists_empty :
    ∃ S : St, ∀ x : St, St.mem x S ↔ False


/- St definitions -/


noncomputable def St.general_uni (A : St) : St :=
    Classical.choose (St.exists_general_uni A)

noncomputable def St.pair (a b : St) : St :=
    Classical.choose (St.exists_pair a b)

noncomputable def St.empty : St :=
    Classical.choose St.exists_empty

noncomputable def St.singlet (a : St) : St :=
    St.pair a a

noncomputable def St.uni (A B : St) : St :=
    St.general_uni (St.pair A B)


/- St equivalence -/


@[refl]
theorem St.eq_rfl (A : St) : A =st A := by
    apply (St.ext A A).mp
    intro x
    rfl

theorem St.eq_symm {A B : St} : (A =st B) → (B =st A) := by
   intro hAB
   replace hAB := (St.ext A B).mpr hAB
   apply (St.ext B A).mp
   intro x
   apply Iff.symm
   exact (hAB x)

theorem St.eq_trans {A B C : St} :
    (A =st B) → (B =st C) → (A =st C) := by

  intro hAB hBC
  replace hAB := (St.ext A B).mpr hAB
  replace hBC := (St.ext B C).mpr hBC
  apply (St.ext A C).mp
  intro x
  apply (Iff.trans (hAB x) (hBC x))

instance : Trans St.eq St.eq St.eq where
  trans := St.eq_trans

instance : Equivalence St.eq :=
⟨
  St.eq_rfl,
  @St.eq_symm,
  @St.eq_trans
⟩


@[simp]
theorem St.mem_congr_right {A B x : St} (h : A =st B) :
  St.mem x A ↔ St.mem x B :=


  (St.ext A B).mpr h x


/- St theorems -/


theorem St.mem_general_uni (A : St) :
  ∀ x : St, St.mem x (St.general_uni A) ↔ ∃ y :
    St, St.mem y A ∧ St.mem x y :=

  Classical.choose_spec (St.exists_general_uni A)

theorem St.mem_pair (a b : St) :
  ∀ x : St, St.mem x (St.pair a b) ↔ ((x =st a) ∨ (x =st b)) :=

  Classical.choose_spec (St.exists_pair a b)

theorem St.mem_empty (x : St) : St.mem x St.empty ↔ False :=

  (Classical.choose_spec St.exists_empty) x

theorem St.mem_singlet (a : St) :
  ∀ x : St, St.mem x (St.singlet a) ↔ (x =st a) := by

  intro x

  -- St.mem x (St.pair a a) <-> x = a
  unfold St.singlet

  -- (h: St.mem x (St.pair a a) ↔ (x = a ∨ x = a))
  have h := St.mem_pair a a x

  constructor
  · /- St.mem x (St.pair a a) -> x = a -/

    -- (hxmempair : St.mem x (St.pair a a))
    intro hxmempair

    -- (h: x = a ∨ x = a)
    replace h := h.mp hxmempair

    rcases h with ha | ha
    · exact ha
    · exact ha

  · /- x = a -> St.mem x (St.pair a a) -/

    intro ha

    have haha : (x =st a) ∨ (x =st a) := by
        left
        exact ha

    -- (h: St.mem x (St.pair a a))
    replace h := h.mpr haha
    exact h

theorem St.pair_symm (a b : St) : St.pair a b =st St.pair b a := by
    apply (St.ext (St.pair a b) (St.pair b a)).mp
    intro x

    have hmemxpair : ∀ c d : St,
        St.mem x (St.pair c d) → St.mem x (St.pair d c) := by

        intro c d hxmemcd
        apply (St.mem_pair d c x).mpr
        have hxeqcxeqd := (St.mem_pair c d x).mp hxmemcd
        rcases hxeqcxeqd with hxeqc | hxeqd
        · right
          exact hxeqc
        · left
          exact hxeqd

    constructor
    · exact (hmemxpair a b)
    · exact (hmemxpair b a)

theorem St.mem_uni (A B : St) :
    ∀ x : St, St.mem x (St.uni A B) ↔ St.mem x A ∨ St.mem x B := by

    -- ∀ x : St, St.mem x (St.uni A B) ↔ St.mem x A ∨ St.mem x B
    -- exists (St.uni A B)

    -- St.mem x (St.uni A B) ↔ St.mem x A ∨ St.mem x B
    intro x

    -- St.mem x (St.general_uni (St.pair A B)) ↔ St.mem x A ∨ St.mem x B
    unfold St.uni

    -- (h1 : St.mem x (St.general_uni (St.pair A B)) ↔
    --  ∃ y : St, St.mem y (St.pair A B) ∧ St.mem x y)
    --
    have h1 := St.mem_general_uni (St.pair A B) x

    have h2 :
        (∃ y : St, St.mem y (St.pair A B) ∧ St.mem x y) ↔
        St.mem x A ∨ St.mem x B := by

        constructor
        · /- ∃ y : St, St.mem y (St.pair A B) ∧ St.mem x y ->
            St.mem x A ∨ St.mem x B -/

          -- (h: ∃ y : St, St.mem y (St.pair A B) ∧ St.mem x y )
          -- St.mem x A ∨ St.mem x B
          intro h

          -- (hy_pair : St.mem y (St.pair A B))
          -- (hxy : St.mem x y)
          obtain ⟨y, hy_pair, hxy⟩ := h

          -- (hyAB : y = A ∨ y = B)
          have hyAB := (St.mem_pair A B y).mp hy_pair

          rcases hyAB with hyA | hyB
          · /- y = A -/
            left
            rw [(St.mem_congr_right hyA).symm]
            exact hxy
          · /- y = B -/
            right
            rw [(St.mem_congr_right hyB).symm]
            exact hxy

        · /- St.mem x A ∨ St.mem x B ->
            ∃ y : St, St.mem y (St.pair A B) ∧ St.mem x y -/

          intro h

          have hxmemY_ymempairANDxmemY :
            ∀ y z : St, St.mem x y → St.mem y (St.pair y z) ∧ St.mem x y := by

            intro y z hxy
            constructor
            · /- St.mem y (St.pair y z) -/
              have hyyoryz : (y =st y) ∨ (y =st z) := by
                left
                rfl
              have hy_pair := (St.mem_pair y z y).mpr hyyoryz
              exact hy_pair

            · /- St.mem x y -/
              exact hxy

          rcases h with hxA | hxB
          · /- hxA: St.mem x A -/
            exists A
            have hxmemA_AmempairANDxmemA :=
                (hxmemY_ymempairANDxmemY A B hxA)
            exact hxmemA_AmempairANDxmemA

          · /- hxB: St.mem x B -/
            exists B
            have hxmemB_BmempairANDxmemB :=
                (hxmemY_ymempairANDxmemY B A hxB)
            rw [St.mem_congr_right (St.pair_symm B A)] at hxmemB_BmempairANDxmemB
            exact hxmemB_BmempairANDxmemB

    exact h1.trans h2


theorem St.set_uni (A B : St) :
    ∃ U : St, ∀ x : St, St.mem x U ↔ St.mem x A ∨ St.mem x B := by

    exists (St.uni A B)
    exact St.mem_uni A B

theorem St.pair_eq_uni_singet (a b : St) :
    St.pair a b =st St.uni (St.singlet a) (St.singlet b) := by

    apply (St.ext (St.pair a b) (St.uni (St.singlet a) (St.singlet b))).mp

    intro x
    rw [St.mem_pair a b x]
    rw [St.mem_uni (St.singlet a) (St.singlet b) x]
    rw [St.mem_singlet a x]
    rw [St.mem_singlet b x]

theorem St.set_non_empty {A : St} (h : (A =st St.empty) → False) :
    ∃ x : St, St.mem x A := by

    -- ∃ x : St, St.mem x A
    -- ((∃ x : St, St.mem x A) -> False) -> False
    apply Classical.not_not.mp

    -- (hx : (∃ x : St, St.mem x A) -> False)
    -- ((∃ x : St, St.mem x A) -> False) -> False
    -- False
    intro hx

    -- False
    -- A = St.empty
    apply h

    -- A = St.empty
    -- (x : St) : St.mem x A ↔ St.mem x St.empty
    apply (St.ext A St.empty).mp

    -- (x : St) : St.mem x A ↔ St.mem x St.empty
    -- St.mem x A ↔ St.mem x St.empty
    intro x

    constructor
    · /- St.mem x A -> St.mem x St.empty -/

      -- St.mem x A -> St.mem x St.empty
      -- (hA : St.mem x A)
      -- St.mem x St.empty
      intro hA

      exfalso
      apply hx
      exists x

    · /- St.mem x empyt -> St.mem x A -/
      intro hempty
      exfalso
      apply (St.mem_empty x).mp
      exact hempty

theorem St.uni_ass (A B C : St) :
    St.uni (St.uni A B) C =st St.uni A (St.uni B C) := by

    apply (St.ext (St.uni (St.uni A B) C) (St.uni A (St.uni B C))).mp
    intro x

    constructor
    · /- St.mem x (St.uni (St.uni A B) C) -> St.mem x (St.uni A (St.uni B C)) -/

      intro h
      rw [St.mem_uni] at h
      rw [St.mem_uni]
      rw [St.mem_uni]
      rcases h with hAB | hC
      ·
        rw [St.mem_uni] at hAB

        rcases hAB with hA | hB
        ·
          left
          exact hA
        ·
          right
          left
          exact hB
      ·
        right
        right
        exact hC

    · /-  St.mem x (St.uni A (St.uni B C)) -> St.mem x (St.uni (St.uni A B) C) -/

      intro h
      rw [St.mem_uni] at h
      rw [St.mem_uni]
      rw [St.mem_uni]

      rcases h with hA | hBC
      ·
        left
        left
        exact hA
      ·
        rw [St.mem_uni] at hBC

        rcases hBC with hB | hC
        ·
          left
          right
          exact hB
        ·
          right
          exact hC

@[simp]
theorem St.uni_comm (A B : St) : St.uni A B =st St.uni B A := by

    apply (St.ext (St.uni A B) (St.uni B A )).mp
    intro x

    rw [St.mem_uni]
    rw [St.mem_uni]
    constructor
    · intro h
      apply Or.symm
      exact h
    · intro h
      apply Or.symm
      exact h

@[simp]
theorem St.uni_congr_left {A B C : St} (h : A =st B) :
  St.uni A C =st St.uni B C := by

  apply (St.ext (St.uni A C) (St.uni B C)).mp
  intro x

  have hxAeqxB : St.mem x A ↔ St.mem x B := St.mem_congr_right h

  simp only [St.mem_uni]

  constructor
  · intro hxAC
    rcases hxAC with hA | hC
    · left
      apply hxAeqxB.mp
      exact hA
    · right
      exact hC

  · intro hxBC
    rcases hxBC with hB | hC
    · left
      apply hxAeqxB.mpr
      exact hB
    · right
      exact hC

@[simp]
theorem St.uni_congr_right {A B C : St} (h : A =st B) :
  St.uni C A =st St.uni C B :=

  calc
    St.uni C A
        =st St.uni A C := by apply St.uni_comm
    _   =st St.uni B C := by apply St.uni_congr_left h
    _   =st St.uni C B := by apply St.uni_comm


theorem St.uni_idem (A : St) : St.uni A A =st A := by
    apply (St.ext (St.uni A A) A).mp
    intro x
    rw [St.mem_uni]

    constructor
    · intro h
      rcases h with hA | hA
      · exact hA
      · exact hA
    · intro h
      left
      exact h

theorem St.uni_empty (A : St) : St.uni A St.empty =st A := by
    apply (St.ext (St.uni A St.empty) A).mp
    intro x
    rw [St.mem_uni]

    constructor
    · intro h
      rcases h with hA | hempty
      · exact hA
      · exfalso
        apply (St.mem_empty x).mp
        exact hempty
    · intro h
      left
      exact h


/- St.inter & diff definitions -/


axiom St.inter : St → St → St
axiom St.mem_inter (A B : St) :
    ∀ x : St, St.mem x (St.inter A B) ↔ St.mem x A ∧ St.mem x B

axiom St.diff : St → St → St
axiom St.mem_diff (A B : St) :
    ∀ x : St, St.mem x (diff A B) ↔ St.mem x A ∧ (St.mem x B → False)


/- St.inter congruence -/

@[simp]
theorem St.inter_congr_right {A B C : St} (h : A =st B) :
  St.inter A C =st St.inter B C := by

  apply (St.ext (St.inter A C) (St.inter B C)).mp
  intro x

  have hxAeqxB : St.mem x A ↔ St.mem x B := St.mem_congr_right h

  simp only [St.mem_inter]

  constructor
  · intro hxAC
    obtain ⟨hA, hC⟩ := hxAC
    constructor
    · apply hxAeqxB.mp
      exact hA
    · exact hC

  · intro hxBC
    obtain ⟨hB, hC⟩ := hxBC
    constructor
    · apply hxAeqxB.mpr
      exact hB
    · exact hC


/- St.inter & diff properties -/


theorem St.inter_empty (A : St) : St.inter A St.empty =st St.empty := by
    apply (St.ext (St.inter A St.empty) St.empty).mp
    intro x
    rw [St.mem_inter]

    constructor
    · intro h
      obtain ⟨ha, hempty⟩ := h
      exact hempty
    · intro h
      constructor
      · /- St.mem x A -/
        exfalso
        replace h := (St.mem_empty x).mp h
        exact h
      · exact h

theorem St.inter_idem (A : St) : St.inter A A =st A := by
    apply (St.ext (St.inter A A) A).mp
    intro x
    rw [St.mem_inter]

    constructor
    · intro h
      obtain ⟨hA1, hA2⟩ := h
      exact hA1
    · intro h
      constructor
      · /- St.mem x A -/
        exact h
      · /- St.mem x A -/
        exact h

@[simp]
theorem St.inter_comm (A B : St) : St.inter A B =st St.inter B A := by
    apply (St.ext (St.inter A B) (St.inter B A)).mp
    intro x
    rw [St.mem_inter]
    rw [St.mem_inter]

    constructor
    · intro h
      obtain ⟨hA, hB⟩ := h
      constructor
      · /- St.mem x B -/
        exact hB
      · /- St.mem x A -/
        exact hA
    · intro h
      obtain ⟨hB, hA⟩ := h
      constructor
      · /- St.mem x A -/
        exact hA
      · /- St.mem x B -/
        exact hB

@[simp]
theorem St.inter_congr_left {A B C : St} (h : A =st B) :
  St.inter C A =st St.inter C B := by

  calc
    St.inter C A =st St.inter A C := by apply St.inter_comm
    _         =st St.inter B C := by apply St.inter_congr_right h
    _         =st St.inter C B := by apply St.inter_comm


theorem St.inter_ass (A B C : St) :
    St.inter (St.inter A B) C =st St.inter A (St.inter B C) := by

    apply (St.ext (St.inter (St.inter A B) C) (St.inter A (St.inter B C))).mp
    intro x
    rw [St.mem_inter]
    rw [St.mem_inter]
    rw [St.mem_inter]
    rw [St.mem_inter]

    constructor
    · intro h
      obtain ⟨hAB, hC⟩ := h
      obtain ⟨hA, hB⟩ := hAB

      constructor
      · exact hA
      · constructor
        · exact hB
        · exact hC

    · intro h
      obtain ⟨hA, hBC⟩ := h
      obtain ⟨hB, hC⟩ := hBC

      constructor
      · constructor
        · exact hA
        · exact hB
      · exact hC

theorem St.uni_distr_left (A B C : St) :
    St.uni A (St.inter B C) =st St.inter (St.uni A B) (St.uni A C) := by

    apply (St.ext (St.uni A (St.inter B C)) (St.inter (St.uni A B) (St.uni A C))).mp
    intro x
    rw [St.mem_uni]
    rw [St.mem_inter]
    rw [St.mem_inter]
    rw [St.mem_uni]
    rw [St.mem_uni]

    constructor
    · intro h
      rcases h with hA | hBandC
      · constructor
        · left
          exact hA
        · left
          exact hA
      · obtain ⟨hB, hC⟩ := hBandC
        constructor
        · right
          exact hB
        · right
          exact hC
    · intro h
      obtain ⟨hAorB, hAorC⟩ := h
      rcases hAorB with hA | hB
      · left
        exact hA
      · rcases hAorC with hA | hC
        · left
          exact hA
        · right
          constructor
          · exact hB
          · exact hC


theorem St.uni_distr_right (A B C : St) :
    St.uni (St.inter B C) A =st St.inter (St.uni B A) (St.uni C A) := by

    calc
      St.uni (St.inter B C) A
        =st St.uni A (St.inter B C) := by
        apply St.uni_comm

      _ =st St.inter (St.uni A B) (St.uni A C) := by
        apply uni_distr_left

      _ =st St.inter (St.uni B A) (St.uni A C) := by

        apply St.inter_congr_right
        apply St.uni_comm

      _ =st St.inter (St.uni B A) (St.uni C A) := by

        apply inter_congr_left
        apply St.uni_comm


theorem St.inter_distr_left (A B C : St) :
    St.inter A (St.uni B C) =st
    St.uni (St.inter A B) (St.inter A C) := by

    apply (St.ext (St.inter A (St.uni B C))
        (St.uni (St.inter A B) (St.inter A C))).mp

    intro x
    rw [St.mem_inter]
    rw [St.mem_uni]
    rw [St.mem_uni]
    rw [St.mem_inter]
    rw [St.mem_inter]

    constructor
    · intro h
      obtain ⟨hA, hBorC⟩ := h
      rcases hBorC with hB | hC
      · left
        constructor
        · exact hA
        · exact hB
      · right
        constructor
        · exact hA
        · exact hC

    · intro h
      rcases h with hAandB | hAandC
      · obtain ⟨hA, hB⟩ := hAandB
        constructor
        · exact hA
        · left
          exact hB
      · obtain ⟨hA, hC⟩ := hAandC
        constructor
        · exact hA
        · right
          exact hC


theorem St.inter_distr_right (A B C : St) :
    St.inter (St.uni B C) A =st
        St.uni (St.inter B A) (St.inter C A) := by

    calc
      St.inter (St.uni B C) A
        =st St.inter A (St.uni B C) := by apply St.inter_comm

      _ =st St.uni (St.inter A B) (St.inter A C) :=
        by apply St.inter_distr_left

      _ =st St.uni (St.inter B A) (St.inter A C) := by

        apply St.uni_congr_left
        apply St.inter_comm

      _ =st St.uni (St.inter B A) (St.inter C A) := by

        apply St.uni_congr_right
        apply St.inter_comm


/- Equality exercises -/


theorem St.empty_not_singlet_empty :
    (St.empty =st St.singlet St.empty) → False := by

    intro h
    replace h := (St.ext St.empty (St.singlet St.empty)).mpr h
    replace h := h St.empty

    apply (St.mem_empty St.empty).mp
    apply h.mpr
    apply (St.mem_singlet St.empty St.empty).mpr
    rfl

theorem St.empty_not_singlet_singlet_empty :
    (St.empty =st St.singlet (St.singlet St.empty)) → False := by

    intro h
    replace h := (St.ext St.empty (
        St.singlet (St.singlet St.empty))).mpr h
    replace h := h (St.singlet St.empty)

    apply (St.mem_empty (St.singlet St.empty)).mp
    apply h.mpr
    apply (St.mem_singlet (St.singlet St.empty)
        (St.singlet St.empty)).mpr
    rfl

theorem St.empty_not_pair_empty_singlet_empty :
    (St.empty =st St.pair St.empty (St.singlet St.empty)) → False := by

    intro h
    replace h := (St.ext St.empty (
        St.pair St.empty (St.singlet St.empty))).mpr h
    replace h := h St.empty

    apply (St.mem_empty St.empty).mp
    apply h.mpr
    apply (St.mem_pair St.empty (St.singlet St.empty) St.empty).mpr

    left
    rfl

theorem St.singlet_empty_not_singlet_singlet_empty :
  (St.singlet St.empty =st
    St.singlet (St.singlet St.empty)) → False := by

  intro h
  apply St.empty_not_singlet_empty
  apply (St.ext St.empty (St.singlet St.empty)).mp
  intro x

  replace h :=
      (St.ext (St.singlet St.empty)
        (St.singlet (St.singlet St.empty))).mpr h

  constructor
  · intro hempty
    replace hempty := (St.mem_empty x).mp hempty
    exfalso
    exact hempty

  · intro hxsingletempty
    replace hxsingletempty :=
        (St.mem_singlet St.empty x).mp hxsingletempty

    have hemptyeqsingletempty : St.empty =st St.singlet St.empty := by
        have hmememptysingletempty :
            St.mem St.empty (St.singlet St.empty) := by

            apply (St.mem_singlet St.empty St.empty).mpr
            rfl

        --apply (St.ext St.empty (St.singlet St.empty)).mp
        replace h := (h St.empty).mp hmememptysingletempty
        apply (St.mem_singlet (St.singlet St.empty) St.empty).mp
        exact h

    rw [St.mem_congr_right hemptyeqsingletempty]

    apply (St.mem_singlet St.empty x).mpr
    exact hxsingletempty

theorem St.singlet_empty_not_pair_empty_singlet_empty :
  (St.singlet St.empty =st
    St.pair St.empty (St.singlet St.empty)) → False := by

  intro h
  apply St.empty_not_singlet_empty
  apply (St.ext St.empty (St.singlet St.empty)).mp
  intro x

  replace h :=
      (St.ext (St.singlet St.empty)
        (St.pair St.empty (St.singlet St.empty))).mpr h

  constructor
  · intro hempty
    replace hempty := (St.mem_empty x).mp hempty
    exfalso
    exact hempty

  · intro hxsingletempty
    replace hxsingletempty :=
        (St.mem_singlet St.empty x).mp hxsingletempty

    have hemptyeqsingletempty : St.empty =st St.singlet St.empty := by
        have hmemsingletemptypairemptysingletempty :
            St.mem (St.singlet St.empty)
                (St.pair St.empty (St.singlet St.empty)) := by

            apply (St.mem_pair St.empty (
                St.singlet St.empty) (St.singlet St.empty)).mpr
            right
            rfl

        replace h := (h (St.singlet St.empty)).mpr
        replace h := h hmemsingletemptypairemptysingletempty
        replace h := (St.mem_singlet St.empty (
            St.singlet St.empty)).mp h
        replace h := St.eq_symm h
        exact h

    rw [St.mem_congr_right hemptyeqsingletempty]

    apply (St.mem_singlet St.empty x).mpr
    exact hxsingletempty

theorem St.singlet_singlet_empty_not_pair_empty_singlet_empty :
  (St.singlet (St.singlet St.empty) =st
    St.pair St.empty (St.singlet St.empty)) → False := by

  intro h
  apply St.empty_not_singlet_empty
  apply (St.ext St.empty (St.singlet St.empty)).mp
  intro x

  replace h :=
      (St.ext (St.singlet (St.singlet St.empty))
        (St.pair St.empty (St.singlet St.empty))).mpr h

  constructor
  · intro hempty
    replace hempty := (St.mem_empty x).mp hempty
    exfalso
    exact hempty

  · intro hxsingletempty
    replace hxsingletempty :=
        (St.mem_singlet St.empty x).mp hxsingletempty

    have hemptyeqsingletempty :
        St.empty =st St.singlet St.empty := by

        have hmememptypairemptysingletempty :
            St.mem St.empty (
                St.pair St.empty (St.singlet St.empty)) := by

            apply (St.mem_pair St.empty (
                St.singlet St.empty) St.empty).mpr
            left
            rfl

        replace h := (h St.empty).mpr
        replace h := h hmememptypairemptysingletempty
        replace h := (St.mem_singlet (
            St.singlet St.empty) St.empty).mp h
        exact h

    rw [St.mem_congr_right hemptyeqsingletempty]

    apply (St.mem_singlet St.empty x).mpr
    exact hxsingletempty


theorem St.eq_singlet {x y : St} (h : x =st y) :
    St.singlet x =st St.singlet y := by

    apply (St.ext (St.singlet x) (St.singlet y)).mp

    intro z

    constructor
    · intro hzSingletX
      have hZeqX : z =st x := (St.mem_singlet x z).mp hzSingletX
      have hZeqY : z =st y := by
        calc
            z =st x := hZeqX
            _ =st y := h
      have hzSingletY := (St.mem_singlet y z).mpr hZeqY
      exact hzSingletY
    · intro hzSingletY
      have hZeqY : z =st y := (St.mem_singlet y z).mp hzSingletY
      have hZeqX : z =st x := by
        calc
            z =st y := hZeqY
            _ =st x := St.eq_symm h
      have hzSingletX := (St.mem_singlet x z).mpr hZeqX
      exact hzSingletX

