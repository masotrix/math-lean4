-- Tipo Nt, valor por defecto zero


inductive Nt : Type
| zero : Nt
| succ : Nt → Nt


-- Addition definition


def add : Nt → Nt → Nt
| a, Nt.zero   => a
| a, Nt.succ b => Nt.succ (add a b)


-- Addition properties


theorem add_zero_right (a : Nt) : add a Nt.zero = a :=
    -- Caso base definicion de "add"
    rfl

theorem add_succ_right (a b : Nt) :
    add a (Nt.succ b) = Nt.succ (add a b) :=

    -- Caso recursivo de definicion de "add"
    rfl

theorem succ_ne_zero (n : Nt) : Nt.succ n ≠ Nt.zero := by
    -- Mover hipotesis de implicancia a hipotesis de teorema
    -- succ n = zero -> False
    -- =>
    -- False
    -- (h: none)
    -- =>
    -- (h: succ n = zero)
    intro h

    -- Contradiccion en hipotesis
    cases h

theorem succ_inj {a b : Nt} (h : Nt.succ a = Nt.succ b) : a = b := by
    -- Inyectividad en definicion de sucesor
    cases h

    -- Reflexion de hipotesis con objetivo
    rfl

theorem succ_func {a b : Nt} (h : a = b) : Nt.succ a = Nt.succ b := by
  rw [h]

theorem add_zero_left (a : Nt) : add Nt.zero a = a := by
  induction a with
  | zero =>
    -- Reflexion de definicion de add con objetivo
    rfl

  | succ a ih =>
    -- Adicion de sucesor por la derecha
    -- add zero (succ a) = succ a
    -- =>
    -- succ (add zero a) = succ a
    rw [add_succ_right]

    -- Hipotesis inductiva
    -- succ (add zero a) = succ a
    -- =>
    -- succ a = succ a
    rw [ih]

theorem add_succ_left (a b : Nt) :
    add (Nt.succ a) b = Nt.succ (add a b) := by

    induction b with

    | zero =>
      -- Adicion de cero por la derecha
      -- add (succ a) zero = succ (add a zero)
      -- =>
      -- succ a = succ a
      rw [add_zero_right]
      rfl

    | succ b ih =>
      -- Adicion de sucesor por la derecha
      -- add (succ a) (succ b) = succ (add a (succ b))
      -- =>
      -- succ (add (succ a) b) = succ (add a (succ b))
      rw [add_succ_right]

      -- Adicion de sucesor por la derecha
      -- succ (add (succ a) b) = succ (add a (succ b))
      -- =>
      -- succ (add (succ a) b) = succ (succ (add a b)) 
      rw [add_succ_right]

      -- Hipotesis inductiva
      -- succ (add (succ a) b) = succ (succ (add a b))
      -- =>
      -- succ (succ (add a b) = succ (succ (add a b)) 
      rw [ih]

theorem add_comm (a b : Nt) :
    add a b = add b a := by

    induction a with

    | zero =>
      -- Adicion de cero por la derecha
      -- add zero b = add b zero
      -- =>
      -- b = add b zero
      rw [add_zero_right]

      -- Adicion de cero por la izquierda
      -- b = add b zero
      -- =>
      -- b = b
      rw [add_zero_left]

    | succ a ih =>
      -- Adicion de sucesor por la izquierda
      -- add (succ a) b = add b (succ a)
      -- =>
      -- succ (add a b) = add b (succ a)
      rw [add_succ_left]

      -- Adicion de sucesor por la derecha
      -- succ (add a b) = add b (succ a)
      -- =>
      -- succ (add a b) = succ (add b a)
      rw [add_succ_right]

      -- Sucesor funcion inyectiva
      -- succ (add a b) = succ (add b a)
      -- =>
      -- add a b = add b a
      apply succ_func

      -- Hipotesis inductiva
      -- add a b = add b a
      -- =>
      -- add a b = add a b
      rw [ih]

theorem add_ass (a b c : Nt) :
    add a (add b c) = add (add a b) c := by

    induction c with

    | zero =>
      -- Adicion de cero por la derecha
      -- add a (add b zero) = add (add a b) zero
      -- =>
      -- add a b = add (add a b) zero
      rw [add_zero_right]

      -- Adicion de cero por la derecha
      -- add a b = add (add a b) zero
      -- =>
      -- add a b = add a b
      rw [add_zero_right]

    | succ c ih =>
      -- Adicion de sucesor por la derecha
      -- add a (add b (succ c)) = add (add a b) (succ c)
      -- =>
      -- add a (succ (add b c)) = add (add a b) (succ c)
      rw [add_succ_right]

      -- Adicion de sucesor por la derecha
      -- add a (succ (add b c)) = add (add a b) (succ c)
      -- =>
      -- succ (add a (add b c)) = add (add a b) (succ c)
      rw [add_succ_right]

      -- Adicion de sucesor por la derecha
      -- succ (add a (add b c)) = add (add a b) (succ c)
      -- =>
      -- succ (add a (add b c)) = succ (add (add a b) c)
      rw [add_succ_right]

      -- Sucesor funcion inyectiva
      -- succ (add a (add b c) = succ (add (add a b) c)
      -- =>
      -- add a (add b c) = add (add a b) c
      apply succ_func

      -- Hipotesis inductiva
      -- add a (add b c) = add (add a b) c
      -- =>
      -- add a (add b c) = add a (add b c)
      rw [ih]

theorem add_canc_left {a b c : Nt}
    (h : add a b = add a c) : b = c := by

    induction a with
    | zero =>
      -- Adicion de zero por la izquierda
      -- add zero b = add zero c
      -- =>
      -- b = add zero c
      rw [add_zero_left] at h

      -- Adicion de zero por la izquierda
      -- b = add zero c
      -- =>
      -- b = c
      rw [add_zero_left] at h

      exact h

    | succ a ih =>
      -- Adicion de sucesor por la izquierda
      -- add (succ a) b = add (succ a) c
      -- =>
      -- succ (add a b) = add (succ a) c
      rw [add_succ_left] at h

      -- Adicion de sucesor por la izquierda
      -- succ (add a b) = add (succ a) c
      -- =>
      -- succ (add a b) = succ (add a c)
      rw [add_succ_left] at h

      -- Sucesor funcion inyectiva
      -- succ (add a b) = succ (add a c)
      -- =>
      -- add a b = add a c
      replace h := succ_inj h

      -- Hipotesis inductiva
      -- add a b = add a c
      -- =>
      -- b = c
      replace h := ih h

      exact h

theorem add_canc_right {a b c : Nt}
    (h : add b a = add c a) : b = c := by

    rw [add_comm] at h
    conv at h =>
        rhs
        rw [add_comm]

    replace h := add_canc_left h

    exact h

theorem add_const_left {a b c : Nt}
    (h : a = b) : add c a = add c b := by

  induction c with
  | zero =>

    -- Adicion de zero por la derecha
    -- add a zero = add b zero
    -- =>
    -- a = b
    repeat rw [add_zero_left]
    exact h

  | succ c ih =>

    -- Adicion de sucesor por la derecha
    -- add (succ c) a = add (succ c) b 
    -- =>
    -- succ (add c a ) = succ (add c b )
    repeat rw [add_succ_left]

    -- Sucesor funcion
    -- succ (add c a) = succ (add c b)
    -- =>
    -- add c a = add c b
    apply succ_func

    -- Hipotesis inductiva
    -- add c a = add c b
    -- =>
    -- a = b
    apply ih

theorem add_const_right {a b c : Nt}
    (h : a = b) : add a c = add b c := by

    rw [add_comm]
    conv =>
        rhs
        rw [add_comm]

    apply add_const_left
    exact h

theorem ne_add_canc_left {a b c : Nt} (h: add a b ≠ add a c) :
    b ≠ c := by

    -- Hipotesis de implicancia a hipotesis de teorema
    -- (heq : none)
    -- =>
    -- (heq : b = c)
    -- b ≠ c
    -- =>
    -- False
    intro heq

    -- Desigualdad en hipotesis h
    -- False
    -- <=
    -- add a b = add a c
    apply h

    -- Adicion de constante
    -- add a b = add a c
    -- <=
    -- b = c
    apply add_const_left

    exact heq

theorem ne_add_const_left {a b c : Nt} (h: b ≠ c) :
    add a b ≠ add a c := by

    -- Hipotesis de implicancia a hipotesis de teorema
    -- (heq : none)
    -- =>
    -- (heq : add a b = add a c)
    -- add a b ≠ add ac
    -- =>
    -- False
    intro heq

    -- Desigualdad en hipotesis h
    -- False
    -- <=
    -- b = c
    apply h

    -- Cancelacion de constante
    -- b = c
    -- <=
    -- add a b = add a c
    apply add_canc_left

    exact heq

def Pos (n : Nt) : Prop := n ≠ Nt.zero

theorem add_pos {a b : Nt} (h : Pos a) : Pos (add a b) := by
   induction b with

   | zero =>

     -- Adicion de cero por la derecha
     -- Pos (add a zero)
     -- =>
     -- Pos a
     rw [add_zero_right]
     exact h

   | succ b ih =>

     -- Adicion de sucesor por la derecha
     -- add a (succ b) = zero -> False
     -- =>
     -- succ (add a b) = zero -> False
     rw [add_succ_right]

     -- Mover hipotesis de implicancia a hipotesis de teorema
     -- succ (add a b) = zero -> False
     -- =>
     -- False
     -- (h: a = zero -> False)
     -- =>
     -- (h: succ (add a b) = zero)
     intro h

     -- Sucesor distinto de cero
     -- False
     -- =>
     -- succ (add a b) = zero
     apply succ_ne_zero (add a b)

     exact h

theorem add_equal_zero_then_zero {a b : Nt}
    (h : add a b = Nt.zero) : (a = Nt.zero) ∧ (b = Nt.zero) := by

    induction b with

    | zero =>
      -- Adicion de cero por la derecha
      -- (h : add a zero = zero)
      -- =>
      -- (h : a = zero)
      rw [add_zero_right] at h

      -- Construir conjuncion
      -- (a = zero) ∧ (b = zero)
      -- =>
      -- · (a = zero) · (b = zero)
      constructor

      -- Usar hipotesis h (a = zero)
      -- (a = zero) ∧ (b = zero)
      -- =>
      -- (b = zero)
      · exact h

      -- Usar contexto (b = zero)
      -- (b = zero)
      -- =>
      -- True
      · rfl

    | succ b ih =>

      -- Adicion de sucesor por la derecha
      -- (h : add a (succ b) = zero)
      -- =>
      -- (h : succ (add a b) = zero)
      rw [add_succ_right] at h

      -- Contradiccion en hipotesis del teorema
      cases h

theorem unique_ante {a : Nt} (h : Pos a) :
    ∃ b : Nt, Nt.succ b = a ∧ ∀ b' : Nt, Nt.succ b' = a → b' = b := by

    induction a with
    | zero =>

      -- Contradiccion en hipotesis del teorema
      -- (h : Pos zero)
      -- =>
      -- (h : False)
      contradiction

    | succ a ih =>

      -- Usar 'a' en existencia
      --
      -- ∃ b : Nt,
      --   succ b = succ a ∧
      --   ∀ b' : Nt, succ b' = succ a → b' = b
      --
      -- =>
      --
      -- succ a = succ a ∧
      -- ∀ b' : Nt, succ b' = succ a → b' = a
      exists a

      -- Construir conjuncion
      --
      -- succ a = succ a ∧
      -- ∀ b' : Nt, succ b' = succ a → b' = a
      --
      -- =>
      --
      -- · succ a = succ a
      -- · ∀ b' : Nt, succ b' = succ a → b' = a
      constructor

      · -- Reflexion de igualdad
        -- succ a = succ a
        -- =>
        -- True
        rfl

      · -- Introducir variable b' en hipotesis
        --
        -- ∀ b' : Nt, succ b' = succ a → b' = a
        -- =>
        -- succ b' = succ a → b' = a
        --
        -- (b' : none)
        -- =>
        -- (b' : Nt)
        intro b'

        -- Mover hipotesis de implicancia a hipotesis de teorema
        -- succ b' = succ a -> b' = a
        -- =>
        -- b' = a
        --
        -- (h: Pos a)
        -- =>
        -- (h: succ b' = succ a)
        intro h

        -- Inyectividad de sucesor
        -- (h: succ b' = succ a)
        -- =>
        -- (h: b' = a)
        replace h := succ_inj h

        -- Matchear objetivo con hipotesis
        exact h


/-
-- Ejemplos

open Nt

def one   : Nt := succ zero
def two   : Nt := succ one
def three : Nt := succ two

notation a " +ₚ " b => add a b
notation a " *ₚ " b => mul a b

#eval (two +ₚ one)
#eval (two *ₚ three)

def toNat : Nt → Nat
| Nt.zero => 0
| Nt.succ n => Nat.succ (toNat n)

#eval toNat (two +ₚ one)    -- 3
#eval toNat (two *ₚ three)  -- 6
-/
