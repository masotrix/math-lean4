import St.Axioms


/- Set succ Axioms -/


axiom St.set_exists_succ (n : St) :
    ∃ S : St, ∀ x : St, St.mem x S ↔ St.mem x (St.uni n (St.singlet n))

noncomputable def St.set_succ (x : St) : St :=
    Classical.choose (St.set_exists_succ x)

theorem St.mem_succ (n : St) :
  ∀ x : St, St.mem x (St.set_succ n) ↔
    St.mem x (St.uni n (St.singlet n)) :=

  Classical.choose_spec (St.set_exists_succ n)


/- Set Nt definition -/


axiom St.set_exists_infinity :
    ∃ S : St, St.mem St.empty S ∧
        ∀ y : St, St.mem y S → St.mem (St.set_succ y) S

noncomputable def St.set_Inf : St :=
    Classical.choose St.set_exists_infinity

theorem St.mem_Inf :
    St.mem St.empty St.set_Inf ∧
        ∀ y : St, St.mem y St.set_Inf →
            St.mem (St.set_succ y) St.set_Inf :=

    Classical.choose_spec St.set_exists_infinity

theorem St.mem_Inf_empty : St.mem St.empty set_Inf :=
  mem_Inf.1

theorem St.mem_Inf_succ (y : St) (h : St.mem y set_Inf) :
  St.mem (St.set_succ y) set_Inf :=

  St.mem_Inf.2 y h

def St.is_Nt (x : St) : Prop := ∀ P : St → Prop,
  P St.empty → (∀ n, P n → P (St.set_succ n)) → P x

noncomputable def St.set_Nt : St :=
    Classical.choose (set_exists_specification set_Inf St.is_Nt)

theorem St.mem_set_Nt (x : St) : 
  St.mem x set_Nt ↔ St.mem x set_Inf ∧ is_Nt x :=
  Classical.choose_spec (set_exists_specification set_Inf is_Nt) x

theorem St.set_Nt_induct (P : St → Prop)
  (base : P St.empty)
  (step : ∀ x, P x → P (St.set_succ x))
  : ∀ x, St.mem x set_Nt → P x := by

  intro x h_mem

  rw [St.mem_set_Nt] at h_mem

  let h_is_Nt := h_mem.2

  apply h_is_Nt P
  · exact base
  · exact step


/- Nt definition -/


axiom Nt : Type
axiom Nt.zero : Nt
axiom Nt.succ : Nt → Nt
axiom Nt.eq : Nt → Nt → Prop
infix:50 " =nt " => Nt.eq

axiom Nt.eq_rfl {a : Nt} : a =nt a
axiom Nt.eq_symm {a b : Nt} : (a =nt b) → (b =nt a)
axiom Nt.eq_trans {a b c : Nt} : (a =nt b) → (b =nt c) → (a =nt c)
instance : Trans Nt.eq Nt.eq Nt.eq where trans := Nt.eq_trans


/- St.from_Nt Axioms -/


axiom St.from_Nt : Nt → St

axiom St.from_Nt_eq (a b : Nt) :
    (a =nt b) ↔ (St.from_Nt a =st St.from_Nt b)

axiom St.from_Nt_mem (n : Nt) :
    St.mem (St.from_Nt n) St.set_Nt

axiom Nt.from_St_mem {x : St} :
    St.mem x St.set_Nt → ∃ n : Nt, St.from_Nt n =st x

axiom St.from_Nt_zero :
    St.from_Nt Nt.zero =st St.empty

axiom St.from_Nt_succ (n : Nt) :
    St.from_Nt (Nt.succ n) =st St.set_succ (St.from_Nt n)


/- Succ properties -/


theorem Nt.succ_ne_zero (n : Nt) :
  (Nt.succ n =nt Nt.zero) → False := by

  intro h

  have h_st : St.set_succ (St.from_Nt n) =st St.empty := calc
    St.set_succ (St.from_Nt n)
    _ =st St.from_Nt (Nt.succ n) := St.eq_symm (St.from_Nt_succ n)
    _ =st St.from_Nt Nt.zero     := (St.from_Nt_eq _ _).1 h
    _ =st St.empty               := St.from_Nt_zero

  have hmem_self : St.mem (St.from_Nt n)
    (St.set_succ (St.from_Nt n)) := by

    rw [St.mem_succ]
    rw [St.mem_uni]
    right
    rw [St.mem_singlet]

  rw [St.mem_congr_right h_st] at hmem_self
  rw [St.mem_empty] at hmem_self
  exact hmem_self

axiom St.set_succ_inj {A B : St} :
    (St.set_succ A =st St.set_succ B) → (A =st B)

theorem Nt.succ_inj {a b : Nt} (h : (Nt.succ a =nt Nt.succ b)) :
  a =nt b := by

  have h_st : St.set_succ (St.from_Nt a) =st
    St.set_succ (St.from_Nt b) :=

    calc
        St.set_succ (St.from_Nt a)
        _ =st St.from_Nt (Nt.succ a) := St.eq_symm (St.from_Nt_succ a)
        _ =st St.from_Nt (Nt.succ b) := (St.from_Nt_eq _ _).1 h
        _ =st St.set_succ (St.from_Nt b) := St.from_Nt_succ b

  have h_repr_eq : St.from_Nt a =st St.from_Nt b :=
    St.set_succ_inj h_st

  exact (St.from_Nt_eq a b).2 h_repr_eq

axiom St.set_succ_congr {A B : St} :
    (A =st B) → (St.set_succ A =st St.set_succ B)

theorem Nt.succ_congr {a b : Nt} :
  (a =nt b) → ((Nt.succ a) =nt (Nt.succ b)) := by

  intro h

  have h_st : St.from_Nt a =st St.from_Nt b := (St.from_Nt_eq a b).1 h

  apply (St.from_Nt_eq _ _).2

  calc
    St.from_Nt (Nt.succ a)
    _ =st St.set_succ (St.from_Nt a) := St.from_Nt_succ a
    _ =st St.set_succ (St.from_Nt b) := St.set_succ_congr h_st
    _ =st St.from_Nt (Nt.succ b)  := St.eq_symm (St.from_Nt_succ b)


/- Nt Induction -/


axiom Nt.prop_congr {P : Nt → Prop} {a b : Nt} :
  (a =nt b) → P a → P b

theorem Nt.induction (P : Nt → Prop)
  (base : P Nt.zero)
  (step : ∀ (n : Nt), P n → P (Nt.succ n))
  : ∀ (n : Nt), P n := by

  intro n

  let Q := λ (x : St) => ∃ (k : Nt), ((St.from_Nt k) =st x) ∧ P k

  have q_base : Q St.empty := by
    exists Nt.zero
    constructor
    · exact St.from_Nt_zero
    · exact base

  have q_step : ∀ (x : St), Q x → Q (St.set_succ x) := by
    intro x h_qx
    rcases h_qx with ⟨k, h_repr_k_eq_x, h_Pk⟩
    exists (Nt.succ k)

    constructor
    ·
      calc
        St.from_Nt (Nt.succ k)
        _ =st St.set_succ (St.from_Nt k) := St.from_Nt_succ k
        _ =st St.set_succ x           := St.set_succ_congr h_repr_k_eq_x

    ·
      apply step k
      exact h_Pk

  have h_Q_n : Q (St.from_Nt n) := by
    apply St.set_Nt_induct Q q_base q_step
    exact St.from_Nt_mem n

  rcases h_Q_n with ⟨k, h_repr_eq, h_Pk⟩

  apply Nt.prop_congr _ h_Pk

  apply (St.from_Nt_eq k n).2
  exact h_repr_eq
