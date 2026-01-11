import St.Axioms


/- Nt definition -/


axiom Nt : Type
axiom Nt.zero : Nt
axiom Nt.succ : Nt → Nt
axiom Nt.eq : Nt → Nt → Prop
notation:50 a " =nt " b => Nt.eq a b

axiom Nt.eq_rfl {a : Nt} : a =nt a
axiom Nt.eq_symm {a b : Nt} : (a =nt b) → (b =nt a)
axiom Nt.eq_trans {a b c : Nt} : (a =nt b) → (b =nt c) → (a =nt c)
instance : Trans Nt.eq Nt.eq Nt.eq where trans := Nt.eq_trans


/- repr_Nt Axioms -/


axiom repr_Nt : Nt → St

axiom repr_Nt_def (a b : Nt) :
    (a =nt b) ↔ (repr_Nt a =st repr_Nt b)

axiom mem_repr_Nt (n : Nt) :
    mem (repr_Nt n) set_Nt

axiom repr_Nt_surj {x : St} :
    mem x set_Nt → ∃ n : Nt, repr_Nt n =st x

axiom zero_repr_Nt :
    repr_Nt Nt.zero =st empty


/- Succ Axioms -/


axiom set_exists_succ (n : St) :
    ∃ S : St, ∀ x : St, mem x S ↔ mem x (uni n (singlet n))

noncomputable def set_succ (x : St) : St :=
    Classical.choose (set_exists_succ x)

theorem mem_succ (n : St) :
  ∀ x : St, mem x (set_succ n) ↔ mem x (uni n (singlet n)) :=

  Classical.choose_spec (set_exists_succ n)

axiom succ_repr_Nt (n : Nt) :
    repr_Nt (Nt.succ n) =st set_succ (repr_Nt n)


/- set_Nt deifinition -/


axiom set_exists_infinity :
    ∃ S : St, mem empty S ∧
        ∀ y : St, mem y S → mem (set_succ y) S

noncomputable def set_Inf : St :=
    Classical.choose set_exists_infinity

theorem mem_Inf :
    mem empty set_Inf ∧
        ∀ y : St, mem y set_Inf → mem (set_succ y) set_Inf :=

    Classical.choose_spec set_exists_infinity

theorem mem_Inf_empty : mem empty set_Inf :=
  mem_Inf.1

theorem mem_Inf_succ (y : St) (h : mem y set_Inf) :
  mem (set_succ y) set_Inf :=

  mem_Inf.2 y h

def is_Nt (x : St) : Prop := ∀ P : St → Prop,
  P empty → (∀ n, P n → P (set_succ n)) → P x

noncomputable def set_Nt : St :=
    Classical.choose (set_exists_specification set_Inf is_Nt)

theorem mem_set_Nt (x : St) : 
  mem x set_Nt ↔ mem x set_Inf ∧ is_Nt x :=
  Classical.choose_spec (set_exists_specification set_Inf is_Nt) x

theorem set_Nt_induct (P : St → Prop)
  (base : P empty)
  (step : ∀ x, P x → P (set_succ x))
  : ∀ x, mem x set_Nt → P x := by

  intro x h_mem

  rw [mem_set_Nt] at h_mem

  let h_is_Nt := h_mem.2

  apply h_is_Nt P
  · exact base
  · exact step


/- Succ properties -/


theorem Nt.succ_ne_zero (n : Nt) :
  (Nt.succ n =nt Nt.zero) → False := by

  intro h

  have h_st : set_succ (repr_Nt n) =st empty := calc
    set_succ (repr_Nt n)
    _ =st repr_Nt (Nt.succ n) := eqst_symm (succ_repr_Nt n)
    _ =st repr_Nt Nt.zero     := (repr_Nt_def _ _).1 h
    _ =st empty               := zero_repr_Nt

  have mem_self : mem (repr_Nt n) (set_succ (repr_Nt n)) := by
    rw [mem_succ]
    rw [mem_uni]
    right
    rw [mem_singlet]

  rw [mem_congr_right h_st] at mem_self
  rw [mem_empty] at mem_self
  exact mem_self

axiom set_succ_inj {A B : St} : (set_succ A =st set_succ B) → (A =st B)

theorem Nt.succ_inj {a b : Nt} (h : (Nt.succ a =nt Nt.succ b)) :
  a =nt b := by

  have h_st : set_succ (repr_Nt a) =st set_succ (repr_Nt b) := calc
    set_succ (repr_Nt a)
    _ =st repr_Nt (Nt.succ a) := eqst_symm (succ_repr_Nt a)
    _ =st repr_Nt (Nt.succ b) := (repr_Nt_def _ _).1 h
    _ =st set_succ (repr_Nt b) := succ_repr_Nt b

  have h_repr_eq : repr_Nt a =st repr_Nt b :=
    set_succ_inj h_st

  exact (repr_Nt_def a b).2 h_repr_eq

axiom set_succ_congr {A B : St} :
    (A =st B) → (set_succ A =st set_succ B)

theorem Nt.succ_congr {a b : Nt} :
  (a =nt b) → ((Nt.succ a) =nt (Nt.succ b)) := by

  intro h

  have h_st : repr_Nt a =st repr_Nt b := (repr_Nt_def a b).1 h

  apply (repr_Nt_def _ _).2

  calc
    repr_Nt (Nt.succ a)
    _ =st set_succ (repr_Nt a) := succ_repr_Nt a
    _ =st set_succ (repr_Nt b) := set_succ_congr h_st
    _ =st repr_Nt (Nt.succ b)  := eqst_symm (succ_repr_Nt b)


/- Nt Induction -/


axiom Nt.prop_congr {P : Nt → Prop} {a b : Nt} :
  (a =nt b) → P a → P b

theorem Nt.induction (P : Nt → Prop)
  (base : P Nt.zero)
  (step : ∀ (n : Nt), P n → P (Nt.succ n))
  : ∀ (n : Nt), P n := by

  intro n

  let Q := λ (x : St) => ∃ (k : Nt), (repr_Nt k =st x) ∧ P k

  have q_base : Q empty := by
    exists Nt.zero
    constructor
    · exact zero_repr_Nt
    · exact base

  have q_step : ∀ (x : St), Q x → Q (set_succ x) := by
    intro x h_qx
    rcases h_qx with ⟨k, h_repr_k_eq_x, h_Pk⟩
    exists (Nt.succ k)

    constructor
    ·
      calc
        repr_Nt (Nt.succ k)
        _ =st set_succ (repr_Nt k) := succ_repr_Nt k
        _ =st set_succ x           := set_succ_congr h_repr_k_eq_x

    ·
      apply step k
      exact h_Pk

  have h_Q_n : Q (repr_Nt n) := by
    apply set_Nt_induct Q q_base q_step
    exact mem_repr_Nt n

  rcases h_Q_n with ⟨k, h_repr_eq, h_Pk⟩

  apply Nt.prop_congr _ h_Pk

  apply (repr_Nt_def k n).2
  exact h_repr_eq
