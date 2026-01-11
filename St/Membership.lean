/- St definition -/


axiom St : Type


/- Membership definition -/


axiom mem : St → St → Prop
axiom eqst : St → St → Prop
notation:50 a " =st " b => eqst a b


/- St properties -/


axiom set_eq (A B : St) :
    (∀ x : St, mem x A ↔ mem x B) ↔ A =st B

axiom set_exists_general_uni (A : St) :
    ∃ S : St, ∀ x : St, mem x S ↔ ∃ y : St, mem y A ∧ mem x y

axiom set_exists_pair (a b : St) :
    ∃ S : St, ∀ x : St, mem x S ↔ ((x =st a) ∨ (x =st b))

axiom set_exists_pow (A : St) :
    ∃ S : St, ∀ x : St, mem x S ↔ ∀ y : St, mem y x → mem y A

axiom set_exists_empty :
    ∃ S : St, ∀ x : St, mem x S ↔ False


/- St definitions -/


noncomputable def general_uni (A : St) : St :=
    Classical.choose (set_exists_general_uni A)

noncomputable def pair (a b : St) : St :=
    Classical.choose (set_exists_pair a b)

noncomputable def empty : St :=
    Classical.choose set_exists_empty

noncomputable def singlet (a : St) : St :=
    pair a a

noncomputable def uni (A B : St) : St :=
    general_uni (pair A B)


/- St equivalence -/


@[refl]
theorem eqst_refl (A : St) : A =st A := by
    apply (set_eq A A).mp
    intro x
    rfl

theorem eqst_symm {A B : St} : (A =st B) → (B =st A) := by
   intro hAB
   replace hAB := (set_eq A B).mpr hAB
   apply (set_eq B A).mp
   intro x
   apply Iff.symm
   exact (hAB x)

theorem eqst_trans {A B C : St} :
    (A =st B) → (B =st C) → (A =st C) := by

  intro hAB hBC
  replace hAB := (set_eq A B).mpr hAB
  replace hBC := (set_eq B C).mpr hBC
  apply (set_eq A C).mp
  intro x
  apply (Iff.trans (hAB x) (hBC x))

instance : Trans eqst eqst eqst where
  trans := eqst_trans

instance : Equivalence eqst :=
⟨
  eqst_refl,
  @eqst_symm,
  @eqst_trans
⟩


@[simp]
theorem mem_congr_right {A B x : St} (h : A =st B) :
  mem x A ↔ mem x B :=


  (set_eq A B).mpr h x


/- St theorems -/


theorem mem_general_uni (A : St) :
  ∀ x : St, mem x (general_uni A) ↔ ∃ y : St, mem y A ∧ mem x y :=

  Classical.choose_spec (set_exists_general_uni A)

theorem mem_pair (a b : St) :
  ∀ x : St, mem x (pair a b) ↔ ((x =st a) ∨ (x =st b)) :=

  Classical.choose_spec (set_exists_pair a b)

theorem mem_empty (x : St) : mem x empty ↔ False :=

  (Classical.choose_spec set_exists_empty) x

theorem mem_singlet (a : St) :
  ∀ x : St, mem x (singlet a) ↔ (x =st a) := by

  intro x

  -- mem x (pair a a) <-> x = a
  unfold singlet

  -- (h: mem x (pair a a) ↔ (x = a ∨ x = a))
  have h := mem_pair a a x

  constructor
  · /- mem x (pair a a) -> x = a -/

    -- (hxmempair : mem x (pair a a))
    intro hxmempair

    -- (h: x = a ∨ x = a)
    replace h := h.mp hxmempair

    rcases h with ha | ha
    · exact ha
    · exact ha

  · /- x = a -> mem x (pair a a) -/

    intro ha

    have haha : (x =st a) ∨ (x =st a) := by
        left
        exact ha

    -- (h: mem x (pair a a))
    replace h := h.mpr haha
    exact h

theorem pair_symm (a b : St) : pair a b =st pair b a := by
    apply (set_eq (pair a b) (pair b a)).mp
    intro x

    have hmemxpair : ∀ c d : St,
        mem x (pair c d) → mem x (pair d c) := by

        intro c d hxmemcd
        apply (mem_pair d c x).mpr
        have hxeqcxeqd := (mem_pair c d x).mp hxmemcd
        rcases hxeqcxeqd with hxeqc | hxeqd
        · right
          exact hxeqc
        · left
          exact hxeqd

    constructor
    · exact (hmemxpair a b)
    · exact (hmemxpair b a)

theorem mem_uni (A B : St) :
    ∀ x : St, mem x (uni A B) ↔ mem x A ∨ mem x B := by

    -- ∀ x : St, mem x (uni A B) ↔ mem x A ∨ mem x B
    -- exists (uni A B)

    -- mem x (uni A B) ↔ mem x A ∨ mem x B
    intro x

    -- mem x (general_uni (pair A B)) ↔ mem x A ∨ mem x B
    unfold uni

    -- (h1 : mem x (general_uni (pair A B)) ↔
    --  ∃ y : St, mem y (pair A B) ∧ mem x y)
    --
    have h1 := mem_general_uni (pair A B) x

    have h2 :
        (∃ y : St, mem y (pair A B) ∧ mem x y) ↔
        mem x A ∨ mem x B := by

        constructor
        · /- ∃ y : St, mem y (pair A B) ∧ mem x y ->
            mem x A ∨ mem x B -/

          -- (h: ∃ y : St, mem y (pair A B) ∧ mem x y )
          -- mem x A ∨ mem x B
          intro h

          -- (hy_pair : mem y (pair A B))
          -- (hxy : mem x y)
          obtain ⟨y, hy_pair, hxy⟩ := h

          -- (hyAB : y = A ∨ y = B)
          have hyAB := (mem_pair A B y).mp hy_pair

          rcases hyAB with hyA | hyB
          · /- y = A -/
            left
            rw [(mem_congr_right hyA).symm]
            exact hxy
          · /- y = B -/
            right
            rw [(mem_congr_right hyB).symm]
            exact hxy

        · /- mem x A ∨ mem x B ->
            ∃ y : St, mem y (pair A B) ∧ mem x y -/

          intro h

          have hxmemY_ymempairANDxmemY :
            ∀ y z : St, mem x y → mem y (pair y z) ∧ mem x y := by

            intro y z hxy
            constructor
            · /- mem y (pair y z) -/
              have hyyoryz : (y =st y) ∨ (y =st z) := by
                left
                rfl
              have hy_pair := (mem_pair y z y).mpr hyyoryz
              exact hy_pair

            · /- mem x y -/
              exact hxy

          rcases h with hxA | hxB
          · /- hxA: mem x A -/
            exists A
            have hxmemA_AmempairANDxmemA :=
                (hxmemY_ymempairANDxmemY A B hxA)
            exact hxmemA_AmempairANDxmemA

          · /- hxB: mem x B -/
            exists B
            have hxmemB_BmempairANDxmemB :=
                (hxmemY_ymempairANDxmemY B A hxB)
            rw [mem_congr_right (pair_symm B A)] at hxmemB_BmempairANDxmemB
            exact hxmemB_BmempairANDxmemB

    exact h1.trans h2


theorem set_uni (A B : St) :
    ∃ U : St, ∀ x : St, mem x U ↔ mem x A ∨ mem x B := by

    exists (uni A B)
    exact mem_uni A B

theorem pair_eq_uni_singet (a b : St) :
    pair a b =st uni (singlet a) (singlet b) := by

    apply (set_eq (pair a b) (uni (singlet a) (singlet b))).mp

    intro x
    rw [mem_pair a b x]
    rw [mem_uni (singlet a) (singlet b) x]
    rw [mem_singlet a x]
    rw [mem_singlet b x]

theorem set_non_empty {A : St} (h : (A =st empty) → False) :
    ∃ x : St, mem x A := by

    -- ∃ x : St, mem x A
    -- ((∃ x : St, mem x A) -> False) -> False
    apply Classical.not_not.mp

    -- (hx : (∃ x : St, mem x A) -> False)
    -- ((∃ x : St, mem x A) -> False) -> False
    -- False
    intro hx

    -- False
    -- A = empty
    apply h

    -- A = empty
    -- (x : St) : mem x A ↔ mem x empty
    apply (set_eq A empty).mp

    -- (x : St) : mem x A ↔ mem x empty
    -- mem x A ↔ mem x empty
    intro x

    constructor
    · /- mem x A -> mem x empty -/

      -- mem x A -> mem x empty
      -- (hA : mem x A)
      -- mem x empty
      intro hA

      exfalso
      apply hx
      exists x

    · /- mem x empyt -> mem x A -/
      intro hempty
      exfalso
      apply (mem_empty x).mp
      exact hempty

theorem uni_ass (A B C : St) :
    uni (uni A B) C =st uni A (uni B C) := by

    apply (set_eq (uni (uni A B) C) (uni A (uni B C))).mp
    intro x

    constructor
    · /- mem x (uni (uni A B) C) -> mem x (uni A (uni B C)) -/

      intro h
      rw [mem_uni] at h
      rw [mem_uni]
      rw [mem_uni]
      rcases h with hAB | hC
      ·
        rw [mem_uni] at hAB

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

    · /-  mem x (uni A (uni B C)) -> mem x (uni (uni A B) C) -/

      intro h
      rw [mem_uni] at h
      rw [mem_uni]
      rw [mem_uni]

      rcases h with hA | hBC
      ·
        left
        left
        exact hA
      ·
        rw [mem_uni] at hBC

        rcases hBC with hB | hC
        ·
          left
          right
          exact hB
        ·
          right
          exact hC

@[simp]
theorem uni_comm (A B : St) : uni A B =st uni B A := by

    apply (set_eq (uni A B) (uni B A )).mp
    intro x

    rw [mem_uni]
    rw [mem_uni]
    constructor
    · intro h
      apply Or.symm
      exact h
    · intro h
      apply Or.symm
      exact h

@[simp]
theorem uni_congr_left {A B C : St} (h : A =st B) :
  uni A C =st uni B C := by

  apply (set_eq (uni A C) (uni B C)).mp
  intro x

  have hxAeqxB : mem x A ↔ mem x B := mem_congr_right h

  simp only [mem_uni]

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
theorem uni_congr_right {A B C : St} (h : A =st B) :
  uni C A =st uni C B :=

  calc
    uni C A
        =st uni A C := by apply uni_comm
    _   =st uni B C := by apply uni_congr_left h
    _   =st uni C B := by apply uni_comm


theorem uni_self (A : St) : uni A A =st A := by
    apply (set_eq (uni A A) A).mp
    intro x
    rw [mem_uni]

    constructor
    · intro h
      rcases h with hA | hA
      · exact hA
      · exact hA
    · intro h
      left
      exact h

theorem uni_empty (A : St) : uni A empty =st A := by
    apply (set_eq (uni A empty) A).mp
    intro x
    rw [mem_uni]

    constructor
    · intro h
      rcases h with hA | hempty
      · exact hA
      · exfalso
        apply (mem_empty x).mp
        exact hempty
    · intro h
      left
      exact h


/- Inter & diff definitions -/


axiom inter : St → St → St
axiom mem_inter (A B : St) :
    ∀ x : St, mem x (inter A B) ↔ mem x A ∧ mem x B

axiom diff : St → St → St
axiom mem_diff (A B : St) :
    ∀ x : St, mem x (diff A B) ↔ mem x A ∧ (mem x B → False)


/- Inter congruence -/

@[simp]
theorem inter_congr_right {A B C : St} (h : A =st B) :
  inter A C =st inter B C := by

  apply (set_eq (inter A C) (inter B C)).mp
  intro x

  have hxAeqxB : mem x A ↔ mem x B := mem_congr_right h

  simp only [mem_inter]

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


/- Inter & diff properties -/


theorem inter_empty (A : St) : inter A empty =st empty := by
    apply (set_eq (inter A empty) empty).mp
    intro x
    rw [mem_inter]

    constructor
    · intro h
      obtain ⟨ha, hempty⟩ := h
      exact hempty
    · intro h
      constructor
      · /- mem x A -/
        exfalso
        replace h := (mem_empty x).mp h
        exact h
      · exact h

theorem inter_self (A : St) : inter A A =st A := by
    apply (set_eq (inter A A) A).mp
    intro x
    rw [mem_inter]

    constructor
    · intro h
      obtain ⟨hA1, hA2⟩ := h
      exact hA1
    · intro h
      constructor
      · /- mem x A -/
        exact h
      · /- mem x A -/
        exact h

@[simp]
theorem inter_comm (A B : St) : inter A B =st inter B A := by
    apply (set_eq (inter A B) (inter B A)).mp
    intro x
    rw [mem_inter]
    rw [mem_inter]

    constructor
    · intro h
      obtain ⟨hA, hB⟩ := h
      constructor
      · /- mem x B -/
        exact hB
      · /- mem x A -/
        exact hA
    · intro h
      obtain ⟨hB, hA⟩ := h
      constructor
      · /- mem x A -/
        exact hA
      · /- mem x B -/
        exact hB

@[simp]
theorem inter_congr_left {A B C : St} (h : A =st B) :
  inter C A =st inter C B := by

  calc
    inter C A =st inter A C := by apply inter_comm
    _         =st inter B C := by apply inter_congr_right h
    _         =st inter C B := by apply inter_comm


theorem inter_ass (A B C : St) :
    inter (inter A B) C =st inter A (inter B C) := by

    apply (set_eq (inter (inter A B) C) (inter A (inter B C))).mp
    intro x
    rw [mem_inter]
    rw [mem_inter]
    rw [mem_inter]
    rw [mem_inter]

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

theorem uni_distr_left (A B C : St) :
    uni A (inter B C) =st inter (uni A B) (uni A C) := by

    apply (set_eq (uni A (inter B C)) (inter (uni A B) (uni A C))).mp
    intro x
    rw [mem_uni]
    rw [mem_inter]
    rw [mem_inter]
    rw [mem_uni]
    rw [mem_uni]

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


theorem uni_distr_right (A B C : St) :
    uni (inter B C) A =st inter (uni B A) (uni C A) := by

    calc
      uni (inter B C) A
        =st uni A (inter B C) := by apply uni_comm

      _ =st inter (uni A B) (uni A C) := by apply uni_distr_left

      _ =st inter (uni B A) (uni A C) := by

        apply inter_congr_right
        apply uni_comm

      _ =st inter (uni B A) (uni C A) := by

        apply inter_congr_left
        apply uni_comm


theorem inter_distr_left (A B C : St) :
    inter A (uni B C) =st uni (inter A B) (inter A C) := by

    apply (set_eq (inter A (uni B C)) (uni (inter A B) (inter A C))).mp
    intro x
    rw [mem_inter]
    rw [mem_uni]
    rw [mem_uni]
    rw [mem_inter]
    rw [mem_inter]

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


theorem inter_distr_right (A B C : St) :
    inter (uni B C) A =st uni (inter B A) (inter C A) := by

    calc
      inter (uni B C) A
        =st inter A (uni B C) := by apply inter_comm

      _ =st uni (inter A B) (inter A C) := by apply inter_distr_left

      _ =st uni (inter B A) (inter A C) := by

        apply uni_congr_left
        apply inter_comm

      _ =st uni (inter B A) (inter C A) := by

        apply uni_congr_right
        apply inter_comm


/- Equality exercises -/


theorem empty_not_singlet_empty :
    (empty =st singlet empty) → False := by

    intro h
    replace h := (set_eq empty (singlet empty)).mpr h
    replace h := h empty

    apply (mem_empty empty).mp
    apply h.mpr
    apply (mem_singlet empty empty).mpr
    rfl

theorem empty_not_singlet_singlet_empty :
    (empty =st singlet (singlet empty)) → False := by

    intro h
    replace h := (set_eq empty (singlet (singlet empty))).mpr h
    replace h := h (singlet empty)

    apply (mem_empty (singlet empty)).mp
    apply h.mpr
    apply (mem_singlet (singlet empty) (singlet empty)).mpr
    rfl

theorem empty_not_pair_empty_singlet_empty :
    (empty =st pair empty (singlet empty)) → False := by

    intro h
    replace h := (set_eq empty (pair empty (singlet empty))).mpr h
    replace h := h empty

    apply (mem_empty empty).mp
    apply h.mpr
    apply (mem_pair empty (singlet empty) empty).mpr

    left
    rfl

theorem singlet_empty_not_singlet_singlet_empty :
  (singlet empty =st singlet (singlet empty)) → False := by

  intro h
  apply empty_not_singlet_empty
  apply (set_eq empty (singlet empty)).mp
  intro x

  replace h :=
      (set_eq (singlet empty) (singlet (singlet empty))).mpr h

  constructor
  · intro hempty
    replace hempty := (mem_empty x).mp hempty
    exfalso
    exact hempty

  · intro hxsingletempty
    replace hxsingletempty :=
        (mem_singlet empty x).mp hxsingletempty

    have hemptyeqsingletempty : empty =st singlet empty := by
        have hmememptysingletempty : mem empty (singlet empty) := by
            apply (mem_singlet empty empty).mpr
            rfl

        --apply (set_eq empty (singlet empty)).mp
        replace h := (h empty).mp hmememptysingletempty
        apply (mem_singlet (singlet empty) empty).mp
        exact h

    rw [mem_congr_right hemptyeqsingletempty]

    apply (mem_singlet empty x).mpr
    exact hxsingletempty

theorem singlet_empty_not_pair_empty_singlet_empty :
  (singlet empty =st pair empty (singlet empty)) → False := by

  intro h
  apply empty_not_singlet_empty
  apply (set_eq empty (singlet empty)).mp
  intro x

  replace h :=
      (set_eq (singlet empty) (pair empty (singlet empty))).mpr h

  constructor
  · intro hempty
    replace hempty := (mem_empty x).mp hempty
    exfalso
    exact hempty

  · intro hxsingletempty
    replace hxsingletempty :=
        (mem_singlet empty x).mp hxsingletempty

    have hemptyeqsingletempty : empty =st singlet empty := by
        have hmemsingletemptypairemptysingletempty :
            mem (singlet empty) (pair empty (singlet empty)) := by
            apply (mem_pair empty (singlet empty) (singlet empty)).mpr
            right
            rfl

        replace h := (h (singlet empty)).mpr
        replace h := h hmemsingletemptypairemptysingletempty
        replace h := (mem_singlet empty (singlet empty)).mp h
        replace h := eqst_symm h
        exact h

    rw [mem_congr_right hemptyeqsingletempty]

    apply (mem_singlet empty x).mpr
    exact hxsingletempty

theorem singlet_singlet_empty_not_pair_empty_singlet_empty :
  (singlet (singlet empty) =st pair empty (singlet empty)) → False := by

  intro h
  apply empty_not_singlet_empty
  apply (set_eq empty (singlet empty)).mp
  intro x

  replace h :=
      (set_eq (singlet (singlet empty))
        (pair empty (singlet empty))).mpr h

  constructor
  · intro hempty
    replace hempty := (mem_empty x).mp hempty
    exfalso
    exact hempty

  · intro hxsingletempty
    replace hxsingletempty :=
        (mem_singlet empty x).mp hxsingletempty

    have hemptyeqsingletempty :
        empty =st singlet empty := by

        have hmememptypairemptysingletempty :
            mem empty (pair empty (singlet empty)) := by
            apply (mem_pair empty (singlet empty) empty).mpr
            left
            rfl

        replace h := (h empty).mpr
        replace h := h hmememptypairemptysingletempty
        replace h := (mem_singlet (singlet empty) empty).mp h
        exact h

    rw [mem_congr_right hemptyeqsingletempty]

    apply (mem_singlet empty x).mpr
    exact hxsingletempty


theorem eqst_singlet {x y : St} (h : x =st y) :
    singlet x =st singlet y := by

    apply (set_eq (singlet x) (singlet y)).mp

    intro z

    constructor
    · intro hzSingletX
      have hZeqX : z =st x := (mem_singlet x z).mp hzSingletX
      have hZeqY : z =st y := by
        calc
            z =st x := hZeqX
            _ =st y := h
      have hzSingletY := (mem_singlet y z).mpr hZeqY
      exact hzSingletY
    · intro hzSingletY
      have hZeqY : z =st y := (mem_singlet y z).mp hzSingletY
      have hZeqX : z =st x := by
        calc
            z =st y := hZeqY
            _ =st x := eqst_symm h
      have hzSingletX := (mem_singlet x z).mpr hZeqX
      exact hzSingletX

