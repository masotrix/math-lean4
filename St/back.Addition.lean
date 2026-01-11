import St.Function


axiom succ : St → St

axiom Nt : Type
axiom Nt.succ : Nt → Nt
axiom Nt.zero : Nt

/- Definicion succ -/


axiom set_succ (n : St) :
    ∃ S : St, ∀ x : St, mem x S ↔ mem x (uni n (singlet n))

noncomputable def succ (x : St) : St :=
    Classical.choose (set_succ x)

theorem mem_succ (n : St) :
  ∀ x : St, mem x (succ n) ↔ mem x (uni n (singlet n)) :=

  Classical.choose_spec (set_succ n)


/- Definicion de Inf -/


axiom set_infinity :
    ∃ S : St,
        mem empty S ∧
        ∀ y : St, mem y S → mem (succ y) S

noncomputable def Inf : St :=
    Classical.choose set_infinity


/- Miembros de Inf -/


theorem mem_Inf :
    mem empty Inf ∧
        ∀ y : St, mem y Inf → mem (succ y) Inf :=

    Classical.choose_spec set_infinity

theorem mem_Inf_empty : mem empty Inf := 
  mem_Inf.1

theorem mem_Inf_succ (y : St) (h : mem y Inf) : mem (succ y) Inf := 
  mem_Inf.2 y h


/- Definicion de Nt -/


def isNt (x : St) : Prop :=
  ∀ P : St → Prop,
    P empty → (∀ n, P n → P (succ n)) → P x

noncomputable def Nt : St :=
    Classical.choose (set_specification Inf isNt)


/- Miembros de Nt -/


theorem mem_Nt (x : St) :
    mem x Nt ↔ (mem x Inf ∧ isNt x) :=

    (Classical.choose_spec (set_specification Inf isNt)) x

theorem mem_Nt_empty : isNt empty := by
    intro P P_empty P_succ
    exact P_empty

theorem mem_Nt_succ (n : St) (h : mem n Nt) : mem (succ n) Nt := by
  replace h := (mem_Nt n).mp h
  obtain ⟨hxmemInf, hxisNt⟩ := h

  apply (mem_Nt (succ n)).mpr

  constructor
  · exact mem_Inf_succ n hxmemInf

  · intro P P_empty P_succ
    apply P_succ
    exact hxisNt P P_empty P_succ


/- Succ como funcion -/


def rel_succ (x y : St) : Prop := y =st succ x

theorem succ_isFunc : isFunc Nt Nt rel_succ := by
  intro x hx
  exists (succ x)
  constructor
  · exact mem_Nt_succ x hx -- Aquí usamos el teorema anterior
  constructor
  · rfl
  · intro z _ hrel_z
    rw [rel_succ] at hrel_z
    exact (eqst_symm hrel_z)

noncomputable def succFunc : Func Nt Nt :=
  defFunc Nt Nt rel_succ succ_isFunc



-- Axioma de recursion

structure IsRecursionSolution {A : St} (a : St)
    (g : Func A A) (f : Func Nt A) : Prop where

  base_eq : f.apply empty (Classical.choose_spec set_infinity).1 =st a
  step_eq : ∀ n : St, ∀ hn : mem n Nt,
            f.apply (succ n) (mem_succ_nt n hn) =st
            g.apply (f.apply n hn) (mem_func f n hn).1


axiom recursion_axiom {A : St} (a : St) (ha : mem a A) (g : Func A A) :
  ∃ f : Func Nt A, IsRecursionSolution a g f

noncomputable def recursion {A : St}
    (a : St) (ha : mem a A) (g : Func A A) : Func Nt A :=

  Classical.choose (recursion_axiom a ha g)

private theorem recursion_spec {A : St}
    (a : St) (ha : mem a A) (g : Func A A) :

  IsRecursionSolution a g (recursion a ha g) :=
  Classical.choose_spec (recursion_axiom a ha g)

theorem recursion_base {A : St}
    (a : St) (ha : mem a A) (g : Func A A) :

  (recursion a ha g).apply
    empty
    (Classical.choose_spec set_infinity).1 =st a :=

  (recursion_spec a ha g).base_eq

theorem recursion_step {A : St}
    (a : St) (ha : mem a A) (g : Func A A)(n : St) (hn : mem n Nt) :

  (recursion a ha g).apply (succ n) (mem_succ_nt n hn) =st
  g.apply
    ((recursion a ha g).apply n hn)
    (mem_func (recursion a ha g) n hn).1 :=

  (recursion_spec a ha g).step_eq n hn


-- Propiedades de succ


theorem mem_self_succ (x : St) : mem x (succ x) := by
    apply (mem_succ x x).mpr
    apply (mem_uni x (singlet x) x).mpr
    right
    apply (mem_singlet x x).mpr
    rfl

theorem succ_ne_empty (n : St) : (succ n =st empty) → False := by
    intro h
    have hempty : mem n empty := by
        rw [← (mem_congr_right h)]
        exact (mem_self_succ n)
    apply (mem_empty n).mp
    apply hempty


theorem succ_func {a b : St} (h : (a =st b)) : (succ a =st succ b) := by
    apply (set_eq (succ a) (succ b)).mp
    intro x

    have hc (n1 n2 : St) (heq : n1 =st n2) :
      mem x (succ n1) → mem x (succ n2) := by

      intro hxmemsuccn1
      apply (mem_succ n2 x).mpr
      replace hxmemsuccn1 := (mem_succ n1 x).mp hxmemsuccn1
      replace hxmemsuccn1 := (mem_uni n1 (singlet n1) x).mp hxmemsuccn1
      apply (mem_uni n2 (singlet n2) x).mpr
      rcases hxmemsuccn1 with hxmemn1 | hxmemsingletn1
      · left
        rw [(mem_congr_right (x:=x) (eqst_symm heq))]
        exact hxmemn1
      · right
        apply (mem_singlet n2 x).mpr
        replace hxmemsingletn1 :=
            (mem_singlet n1 x).mp hxmemsingletn1
        apply (eqst_trans hxmemsingletn1 heq)

    constructor
    · exact (hc a b h)
    · exact (hc b a (eqst_symm h))

/-

theorem succ_mem (h : mem x A) : mem (succ x) (succ A) := by
    apply (mem_succ A (succ x)).mpr
    apply (mem_uni A (singlet A) (succ x)).mpr
    rw [mem_singlet A (succ x)]
-/



/-

theorem succ_inj {a b : St} (hnt : isNt a ∧ isNt b)
    (h : (succ a =st succ b)) : (a =st b) := by


    apply (set_eq a b).mp
    intro x
    constructor
    ·

      intro hxmema

      have heq := (set_eq (succ a) (succ b)).mpr h
      replace heq := heq x
      rw [(mem_succ a x)] at heq
      rw [(mem_succ b x)] at heq
      rw [(mem_uni a (singlet a) x)] at heq
      rw [(mem_uni b (singlet b) x)] at heq

      --rw [succ

-/

/-
    obtain ⟨hnta, hntb⟩ := hnt


    let P (x : St) : Prop := a =st b

    apply (hnta P)
    trace_state
-/
/-
    apply (set_eq a b).mp
    intro x

    replace h := (set_eq (succ a) (succ b)).mpr h
    replace h := (h x)
    obtain ⟨hleft, hright⟩ := h

    have hunisinglet (n1 n2 : St)
        (hsucc : mem x (succ n1) → mem x (succ n2)) :

        mem x (uni n1 (singlet n1)) → mem x (uni n2 (singlet n2)) := by

        intro hunisingletn1
        apply (mem_succ n2 x).mp
        apply hsucc
        apply (mem_succ n1 x).mpr
        apply hunisingletn1

    have hunisingletab := hunisinglet a b hleft 
    have hunisingletba := hunisinglet b a hright

    constructor
    · intro hxmema
      replace hxmema : mem x a ∨ x =st a :=
        left
        exact hxmema
-/


    /-
    trace_state
    rw [(mem_succ a x).mpr] at hleft
    trace_state
    -/
    





/-

theorem succ_func {a b : Nt} (h : a = b) : Nt.succ a = Nt.succ b := by
  rw [h]



axiom add : St → St → St

axiom add_zero_right (a : St) :
  add a empty =st a

axiom add_succ_right (a b : St) :
  add a (succ b) =st succ (add a b)


-/
