namespace Peano

inductive Peano : Type
| zero : Peano
| succ : Peano → Peano

open Peano

notation "ℙ0" => Peano.zero

def add : Peano → Peano → Peano
| a, zero   => a
| a, succ b => succ (add a b)

def mul : Peano → Peano → Peano
| _, zero => zero
| a, succ b => add a (mul a b)

instance : Inhabited Peano := ⟨Peano.zero⟩

def one   : Peano := succ zero
def two   : Peano := succ one
def three : Peano := succ two


-- Add

theorem add_zero_right (a : Peano) : add a zero = a :=
    -- Caso base definicion de "add"
    rfl

theorem add_succ_right (a b : Peano) :
    add a (succ b) = succ (add a b) :=

    -- Caso recursivo de definicion de "add"
    rfl

theorem zero_ne_succ (n : Peano) : zero ≠ succ n := by
    intro h
    cases h

theorem succ_inj {a b : Peano} (h : succ a = succ b) : a = b := by
    cases h
    rfl

theorem add_zero_left (a : Peano) : add zero a = a := by
  induction a with
  | zero =>
    -- Caso base definicion de "add"
    rfl

  | succ a ih =>
    -- Caso recursivo definicion de "add"
    -- add zero (succ a) = succ a => succ (add zero a) = succ a
    rw [add_succ_right]

    -- Hipotesis inductiva
    -- succ (add zero a) = succ a => succ a = succ a
    rw [ih]

theorem add_succ_left (a b : Peano) :
    add (succ a) b = succ (add a b) := by

    induction b with

    | zero =>
      -- Adicion de cero por la derecha
      -- add (succ a) zero = succ (add a zero) => succ a = succ a
      rw [add_zero_right]
      rfl

    | succ b ih =>
      -- Adicion de sucesor por la derecha
      -- add (succ a) (succ b) = succ (add a (succ b)) =>
      -- succ (add (succ a) b) = succ (add a (succ b))
      rw [add_succ_right]

      -- Adicion de sucesor por la derecha
      -- succ (add (succ a) b) = succ (add a (succ b)) =>
      -- succ (add (succ a) b) = succ (succ (add a b)) 
      rw [add_succ_right]

      -- Hipotesis inductiva
      -- succ (add (succ a) b) = succ (succ (add a b)) =>
      -- succ (succ (add a b) = succ (succ (add a b)) 
      rw [ih]

theorem add_comm (a b : Peano) :
    add a b = add b a := by

    induction a with

    | zero =>
      -- Adicion de cero por la derecha
      -- add zero b = add b zero =>
      -- b = add b zero
      rw [add_zero_right]

      -- Adicion de cero por la izquierda
      -- b = add b zero =>
      -- b = b
      rw [add_zero_left]

    | succ a ih =>
      -- Adicion de sucesor por la izquierda
      -- add (succ a) b = add b (succ a) =>
      -- succ (add a b) = add b (succ a)
      rw [add_succ_left]

      -- Adicion de sucesor por la derecha
      -- succ (add a b) = add b (succ a) =>
      -- succ (add a b) = succ (add b a)
      rw [add_succ_right]

      -- Sucesor funcion inyectiva
      -- succ (add a b) = succ (add b a) =>
      -- add a b = add b a
      apply succ_inj

      -- Hipotesis inductiva
      -- add a b = add b a =>
      -- add a b = add a b
      rw [ih]

theorem add_ass (a b c : Peano) :
    add a (add b c) = add (add a b) c := by

    induction c with

    | zero =>
      -- Adicion de cero por la derecha
      -- add a (add b zero) = add (add a b) zero =>
      -- add a b = add (add a b) zero
      rw [add_zero_right]

      -- Adicion de cero por la derecha
      -- add a b = add (add a b) zero =>
      -- add a b = add a b
      rw [add_zero_right]

    | succ c ih =>
      -- Adicion de sucesor por la derecha
      -- add a (add b (succ c)) = add (add a b) (succ c) =>
      -- add a (succ (add b c)) = add (add a b) (succ c)
      rw [add_succ_right]

      -- Adicion de sucesor por la derecha
      -- add a (succ (add b c)) = add (add a b) (succ c) =>
      -- succ (add a (add b c)) = add (add a b) (succ c)
      rw [add_succ_right]

      -- Adicion de sucesor por la derecha
      -- succ (add a (add b c)) = add (add a b) (succ c) =>
      -- succ (add a (add b c)) = succ (add (add a b) c)
      rw [add_succ_right]

      -- Sucesor funcion inyectiva
      -- succ (add a (add b c) = succ (add (add a b) c) =>
      -- add a (add b c) = add (add a b) c
      apply succ_inj

      -- Hipotesis inductiva
      -- add a (add b c) = add (add a b) c =>
      -- add a (add b c) = add a (add b c)
      rw [ih]

theorem add_canc {a b c : Peano}
    (h : add a b = add a c) : b = c := by

    induction a with
    | zero =>
      -- Adicion de zero por la izquierda
      -- add zero b = add zero c =>
      -- b = add zero c
      rw [add_zero_left] at h

      -- Adicion de zero por la izquierda
      -- b = add zero c =>
      -- b = c
      rw [add_zero_left] at h

      exact h

    | succ a ih =>
      -- Adicion de sucesor por la izquierda
      -- add (succ a) b = add (succ a) c =>
      -- succ (add a b) = add (succ a) c
      rw [add_succ_left] at h

      -- Adicion de sucesor por la izquierda
      -- succ (add a b) = add (succ a) c =>
      -- succ (add a b) = succ (add a c)
      rw [add_succ_left] at h

      -- Sucesor funcion inyectiva
      -- succ (add a b) = succ (add a c) =>
      -- add a b = add a c
      replace h := succ_inj h

      -- Hipotesis inductiva
      -- add a b = add a c =>
      -- b = c
      replace h := ih h

      exact h


-- Mul

theorem mul_zero (a : Peano) : mul a zero = zero :=
    -- Caso base de definicion de "mul"
    rfl

theorem mul_succ (a b : Peano) : mul a (succ b) = add a (mul a b) :=
    -- Caso recursivo de definicion de "mul"
    rfl

end Peano


/-
-- Ejemplos

open Peano

notation a " +ₚ " b => add a b
notation a " *ₚ " b => mul a b

#eval (two +ₚ one)
#eval (two *ₚ three)

def toNat : Peano → Nat
| Peano.zero => 0
| Peano.succ n => Nat.succ (toNat n)

#eval toNat (two +ₚ one)    -- 3
#eval toNat (two *ₚ three)  -- 6
-/
