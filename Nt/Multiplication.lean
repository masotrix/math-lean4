import Nt.Order


/- Multiplication definition -/


def mul : Nt → Nt → Nt
| _, Nt.zero => Nt.zero
| a, Nt.succ b => add a (mul a b)


/- Multiplication properties -/


theorem mul_zero_right (a : Nt) : mul a Nt.zero = Nt.zero :=
    -- Caso base de definicion de "mul"
    rfl

theorem mul_succ_right (a b : Nt) :
    mul a (Nt.succ b) = add a (mul a b) :=
    -- Caso recursivo de definicion de "mul"
    rfl

theorem mul_zero_left (a : Nt) : mul Nt.zero a = Nt.zero := by
  induction a with
  | zero =>

    rw [mul_zero_right]

  | succ a ih =>

    -- mul zero (succ a)
    -- =>
    -- add zero (mul zero a)
    rw [mul_succ_right]

    -- add zero (mul zero a)
    -- mul zero a
    rw [add_zero_left]

    exact ih

theorem mul_succ_left (a b : Nt) :
    mul (Nt.succ a) b = add (mul a b) b := by

    induction a with
    | zero =>

        induction b with
        | zero =>

          -- mul (succ zero) zero = add (mul zero zero) zero
          -- mul (succ zero) zero = add zero zero
          rw [mul_zero_left]

          -- mul (succ zero) zero = add zero zero
          -- zero = add zero zero
          rw [mul_zero_right]

          -- zero = add zero zero
          -- zero = zero
          rw [add_zero_left]

        | succ b ih2 =>

          -- (ih2 : mul (succ zero) b = add (mul zero b) b)

          -- mul (succ zero) (succ b) =
          --    add (mul zero (succ b)) (succ b)
          -- =>
          -- add (succ zero) (mul (succ zero) b) =
          --    add (mul zero (succ b)) (succ b)
          rw [mul_succ_right]

          -- add (succ zero) (mul (succ zero) b) =
          --    add (mul zero (succ b)) (succ b)
          -- =>
          -- add (succ zero) (mul (succ zero) b) =
          --    add zero (succ b)
          rw [mul_zero_left]

          -- add (succ zero) (mul (succ zero) b) =
          --    add zero (succ b)
          -- =>
          -- add (succ zero) (add (mul zero b) b) =
          --    add zero (succ b)
          rw [ih2]

          -- add (succ zero) (add (mul zero b) b) = add zero (succ b)
          -- =>
          -- add (succ zero) (add zero b) = add zero (succ b)
          rw [mul_zero_left]

          -- add (succ zero) (add zero b) = add zero (succ b)
          -- =>
          -- add (succ zero) (add zero b) = succ b
          rw [add_zero_left]

          -- add (succ zero) (add zero b) = succ b
          -- succ (add zero (add zero b)) = succ b
          rw [add_succ_left]

          -- succ (add zero (add zero b)) = succ b
          -- succ (add zero b) = succ b
          rw [add_zero_left]

          -- succ (add zero b) = succ b
          -- succ b = succ b
          rw [add_zero_left]

    | succ a ih1 =>

      -- (ih1 : mul (succ a) b = add (mul a b) b)

      induction b with
      | zero =>

        -- zero = add (mul (succ a) zero) zero
        rw [mul_zero_right]

        -- zero = add zero zero
        rw [mul_zero_right]

        -- zero = zero
        rw [add_zero_right]

      | succ b ih2 =>

        -- (ih1 : mul (succ a) (succ b) = add (mul a (succ b) (succ b))
        -- (ih2 : mul (succ (succ a)) b = add (mul (succ a) b) b)

        -- mul (succ (succ a)) (succ b) =
        --      add (mul (succ a) (succ b)) (succ b)
        -- =>
        -- add (succ (succ a)) (mul (succ (succ a)) b) =
        --      add (mul (succ a) (succ b)) (succ b)
        rw [mul_succ_right]

        -- add (succ (succ a)) (mul (succ (succ a)) b) =
        --      add (mul (succ a) (succ b)) (succ b)
        -- =>
        -- add (succ (succ a)) (mul (succ (succ a)) b) =
        --      add (add (succ a) (mul (succ a) b)) (succ b)
        rw [mul_succ_right]

        -- add (succ (succ a)) (mul (succ (succ a)) b) =
        --      add (add (succ a) (mul (succ a) b)) (succ b)
        -- add (succ (succ a)) (mul (succ (succ a)) b) =
        --      succ (add (add (succ a) (mul (succ a) b)) b
        rw [add_succ_right]

        -- add (succ (succ a)) (mul (succ (succ a)) b) =
        --      succ (add (add (succ a) (mul (succ a) b)) b)
        -- =>
        -- add (succ (succ a)) (mul (succ (succ a)) b) =
        --      succ (add (succ (add a (mul (succ a) b))) b)
        rw [add_succ_left]

        -- add (succ (succ a)) (mul (succ (succ a)) b) =
        --      succ (add (succ (add a (mul (succ a) b))) b)
        -- =>
        -- add (succ (succ a)) (mul (succ (succ a)) b) =
        --      succ (succ (add (add a (mul (succ a) b)) b))
        rw [add_succ_left]

        -- add (succ (succ a)) (mul (succ (succ a)) b) =
        --      succ (succ (add (add a (mul (succ a) b)) b))
        -- =>
        -- succ (add (succ a) (mul (succ (succ a)) b)) =
        --      succ (succ (add (add a (mul (succ a) b)) b))
        rw [add_succ_left]

        -- succ (add (succ a) (mul (succ (succ a)) b)) =
        --      succ (succ (add (add a (mul (succ a) b)) b))
        -- succ (succ (add a (mul (succ (succ a)) b))) =
        --      succ (succ (add (add a (mul (succ a) b)) b))
        rw [add_succ_left]

        -- succ (succ (add a (mul (succ (succ a)) b))) =
        --      succ (succ (add (add a (mul (succ a) b)) b))
        -- succ (add a (mul (succ (succ a)) b)) =
        --      succ (add (add a (mul (succ a) b)) b)
        apply succ_func

        -- succ (add a (mul (succ (succ a)) b)) =
        --      succ (add (add a (mul (succ a) b)) b)
        -- add a (mul (succ (succ a)) b) =
        --      add (add a (mul (succ a) b)) b
        apply succ_func

        -- add a (mul (succ (succ a)) b) =
        --      add (add a (mul (succ a) b)) b
        -- add a (mul (succ (succ a)) b) =
        --      add a (add (mul (succ a) b) b)
        rw [← add_ass]

        -- add a (mul (succ (succ a)) b) =
        --      add a (add (mul (succ a) b) b)
        -- mul (succ (succ a)) b =
        --      add (mul (succ a) b) b
        apply add_const_left

        -- mul (succ (succ a)) b =
        --      add (mul (succ a) b) b
        -- mul (succ  a) b =
        --      add (mul a b) b
        apply ih2

        -- mul (succ  a) b =
        --      add (mul a b) b
        -- add (succ a) (mul (succ  a) b) =
        --      add (succ a) (add (mul a b) b)
        apply add_canc_left

        -- add (succ a) (mul (succ  a) b) =
        --      add (succ a) (add (mul a b) b)
        -- mul (succ  a) (succ b) =
        --      add (succ a) (add (mul a b) b)
        rw [← mul_succ_right]

        -- mul (succ  a) (succ b) =
        --      add (succ a) (add (mul a b) b)
        -- add (mul a (succ b)) (succ b) =
        --      add (succ a) (add (mul a b) b)
        rw [ih1]

        -- add (mul a (succ b)) (succ b) =
        --      add (succ a) (add (mul a b) b)
        -- =>
        -- add (add a (mul a b)) (succ b) =
        --      add (succ a) (add (mul a b) b)
        rw [mul_succ_right]

        -- add (add a (mul a b)) (succ b) =
        --      add (succ a) (add (mul a b) b)
        -- add (add a (mul a b)) (succ b) =
        --      succ (add a (add (mul a b) b))
        rw [add_succ_left]

        -- add (add a (mul a b)) (succ b) =
        --      succ (add a (add (mul a b) b))
        -- succ (add (add a (mul a b)) b) =
        --      succ (add a (add (mul a b) b))
        rw [add_succ_right]

        -- succ (add (add a (mul a b)) b) =
        --      succ (add a (add (mul a b) b))
        -- add (add a (mul a b)) b) =
        --      add a (add (mul a b) b))
        apply succ_func

        -- add (add a (mul a b)) b) =
        --      add a (add (mul a b) b))
        -- add a (add (mul a b) b) =
        --      add a (add (mul a b) b)
        rw [add_ass]

theorem mul_comm (a b : Nt) : mul a b = mul b a := by
    induction a with
    | zero =>

      rw [mul_zero_left]
      rw [mul_zero_right]

    | succ a ih1 =>

      -- (ih1: mul a b = mul b a)

      induction b with
      | zero =>

        rw [mul_zero_right]
        rw [mul_zero_left]

      | succ b ih2 =>

        -- (ih1 : mul a (succ b) = mul (succ b) a)
        -- (ih2 : mul a b = mul b a -> mul (succ a) b = mul b (succ a)

        -- mul (succ a) (succ b) = mul (succ b) (succ a)
        -- =>
        -- add (succ a) (mul (succ a) b) = mul (succ b) (succ a)
        rw [mul_succ_right]

        -- add (succ a) (mul (succ a) b) = mul (succ b) (succ a)
        -- =>
        -- add (succ a) (mul (succ a) b) = add (succ b) (mul (succ b) a)
        rw [mul_succ_right]

        -- add (succ a) (mul (succ a) b) = add (succ b) (mul (succ b) a)
        -- =>
        -- add (succ a) (mul (succ a) b) =
        --      add (succ b) (add (mul b a) a)
        rw [mul_succ_left]

        -- add (succ a) (mul (succ a) b) =
        --      add (succ b) (add (mul b a) a)
        -- =>
        -- add (succ a) (add (mul a b) b) =
        --      add (succ b) (add (mul b a) a)
        rw [mul_succ_left]

        -- add (succ a) (add (mul a b) b) =
        --      add (succ b) (add (mul b a) a)
        -- =>
        -- succ (add a (add (mul a b) b)) =
        --      add (succ b) (add (mul b a) a)
        rw [add_succ_left]

        -- succ (add a (add (mul a b) b)) =
        --      add (succ b) (add (mul b a) a)
        -- =>
        -- succ (add a (add (mul a b) b)) =
        --      succ (add b (add (mul b a) a))
        rw [add_succ_left]

        -- succ (add a (add (mul a b) b)) =
        --      succ (add b (add (mul b a) a))
        -- =>
        -- add a (add (mul a b) b) =
        --      add b (add (mul b a) a)
        apply succ_func

        -- add a (add (mul a b) b) =
        --      add b (add (mul b a) a)
        -- =>
        -- add a (add (mul a b) b) =
        --      add b (mul (succ b) a)
        conv =>
            rhs
            rw [← mul_succ_left]

        -- add a (add (mul a b) b) =
        --      add b (mul (succ b) a)
        -- add a (add (mul a b) b) =
        --      add b (mul a (succ b))
        rw [← ih1]

        -- add a (add (mul a b) b) =
        --      add b (mul a (succ b))
        -- =>
        -- add a (add (mul a b) b) =
        --      add b (add a (mul a b))
        rw [mul_succ_right]

        -- add a (add (mul a b) b) =
        --      add b (add a (mul a b))
        -- =>
        -- add a (add (mul a b) b) =
        --      add (add b a) (mul a b)
        conv =>
            rhs
            rw [add_ass]

        -- add a (add (mul a b) b) =
        --      add (add b a) (mul a b)
        -- =>
        -- add a (add (mul a b) b) =
        --      add (add a b) (mul a b)
        conv =>
            rhs
            arg 1
            rw [add_comm]

        -- add a (add (mul a b) b) =
        --      add (add a b) (mul a b)
        -- =>
        -- add a (add (mul a b) b) =
        --      add a (add b (mul a b))
        conv =>
            rhs
            rw [← add_ass]

        -- add a (add (mul a b) b) =
        --      add a (add b (mul a b))
        -- add a (add b (mul a b)) =
        --      add a (add b (mul a b))
        conv =>
            lhs
            arg 2
            rw [add_comm]

theorem mul_zero_then_zero {a b : Nt} :
    mul a b = Nt.zero ↔ a = Nt.zero ∨ b = Nt.zero := by

    constructor
    · /- (habzero : mul a b = zero) -/

      intro habzero

      by_cases ha : a = Nt.zero
      · /- (ha : a = zero) -/
        left
        exact ha

      · /- (ha : a = zero -> False) -/

        by_cases hb : b = Nt.zero
        · /- (hb : b = zero) -/
          right
          exact hb

        · /- (hb : b = zero -> False) -/

          have ⟨c, hac, hcu⟩ := unique_ante ha
          have ⟨d, hbd, hdu⟩ := unique_ante hb
          rw [← hac] at habzero
          rw [← hbd] at habzero
          rw [mul_succ_right] at habzero
          rw [add_succ_left] at habzero
          replace habzero := succ_ne_zero (add c (mul c.succ d)) habzero
          exfalso
          exact habzero

    · /- (habzero : a = zero ∨ b = zero) -/

      intro habzero

      rcases habzero with ha | hb
      · /- (ha : a = zero) -/

        rw [ha]
        rw [mul_zero_left]

      · /- (hb : b = zero) -/

        rw [hb]
        rw [mul_zero_right]

theorem not_zero_not_zero_mul_not_zero (a b : Nt) :
    a ≠ Nt.zero → b ≠ Nt.zero → mul a b ≠ Nt.zero := by

    intro ha hb hab
    replace hab := mul_zero_then_zero.mp hab

    rcases hab with hazero | hbzero
    · apply ha
      exact hazero
    · apply hb
      exact hbzero

theorem mul_distr_right (a b c : Nt) :
    mul a (add b c) = add (mul a b) (mul a c) := by

    induction a with
    | zero =>
      rw [mul_zero_left]
      rw [mul_zero_left]
      rw [mul_zero_left]
      rw [add_zero_left]

    | succ a ih =>

    -- (ih : mul a (add b c) = add (mul a b) (mul a c)

    -- mul (succ a) (add b c) = add (mul (succ a) b) (mul (succ a) c)
    -- add (mul a (add b c)) (add b c) =
    --      add (mul (succ a) b) (mul (succ a) c)
    rw [mul_succ_left]

    -- add (mul a (add b c)) (add b c) =
    --      add (add (mul a b) b) (mul (succ a) c)
    rw [mul_succ_left]

    -- add (mul a (add b c)) (add b c) =
    --      add (add (mul a b) b) (add (mul a c) c)
    rw [mul_succ_left]

    -- add (mul a (add b c)) (add b c) =
    --      add (add (mul a b) b) (add (mul a c) c)
    -- =>
    -- add (add (mul a (add b c)) b) c =
    --      add (add (mul a b) b) (add (mul a c) c)
    rw [add_ass]

    -- add (add (mul a (add b c)) b) c =
    --      add (add (mul a b) b) (add (mul a c) c)
    -- add (add (mul a (add b c)) b) c =
    --      add (add (add (mul a b) b) (mul a c)) c
    rw [add_ass]

    -- add (mul a (add b c)) b =
    --      add (add (mul a b) b) (mul a c)
    apply add_const_right

    -- add (mul a (add b c)) b =
    --      add (add (mul a b) b) (mul a c)
    -- add (mul a (add b c)) b =
    --      add (mul a c) (add (mul a b) b)
    conv =>
        rhs
        rw [add_comm]

    -- add (mul a (add b c)) b =
    --      add (mul a c) (add (mul a b) b)
    -- add (mul a (add b c)) b =
    --      add (add (mul a c) (mul a b)) b
    rw [add_ass]

    -- add (mul a (add b c)) b =
    --      add (add (mul a c) (mul a b)) b
    -- mul a (add b c) =
    --      add (mul a c) (mul a b)
    rw [add_const_right]

    -- mul a (add b c) =
    --      add (mul a c) (mul a b)
    -- mul a (add b c) =
    --      add (mul a b) (mul a c)
    conv =>
        rhs
        rw [add_comm]

    exact ih

theorem mul_distr_left (a b c : Nt) :
    mul (add b c) a = add (mul b a) (mul c a) := by

    rw [mul_comm]

    conv =>
        rhs
        arg 1
        rw [mul_comm]

    conv =>
        rhs
        arg 2
        rw [mul_comm]

    exact mul_distr_right a b c

theorem mul_ass (a b c : Nt) : mul (mul a b) c = mul a (mul b c) := by
    induction c with
    | zero =>
      rw [mul_zero_right]
      rw [mul_zero_right]
      rw [mul_zero_right]

    | succ c ih =>

      -- (ih : mul (mul a b) c = mul a (mul b c))

      -- mul (mul a b) (succ c) = mul a (mul b (succ c))
      -- =>
      -- add (mul a b) (mul (mul a b) c) = mul a (mul b (succ c))
      rw [mul_succ_right]

      -- add (mul a b) (mul (mul a b) c) = mul a (mul b (succ c))
      -- =>
      -- add (mul a b) (mul (mul a b) c) = mul a (add b (mul b c))
      rw [mul_succ_right]

      -- add (mul a b) (mul (mul a b) c) = mul a (add b (mul b c))
      -- =>
      -- add (mul a b) (mul (mul a b) c) =
      --    add (mul a b) (mul a (mul b c))
      rw [mul_distr_right]

      -- add (mul a b) (mul (mul a b) c) =
      --    add (mul a b) (mul a (mul b c))
      -- =>
      -- mul (mul a b) c = mul a (mul b c)
      apply add_const_left

      exact ih

theorem gt_mul_const {a b c : Nt} (h : Pos c) (hgt: gt b a) :
    gt (mul b c) (mul a c) := by

      -- (heq : b = add a d)
      obtain ⟨d, hdpos, heq⟩ := (gt_exists_pos b a).mp hgt

      -- gt (mul b c) (mul a c)
      -- =>
      -- (∃ x : Nt, Pos x ∧ mul b c = add (mul a c) x)
      apply (gt_exists_pos (mul b c) (mul a c)).mpr

      -- (∃ x : Nt, Pos x ∧ mul b c = add (mul a c) x)
      -- =>
      -- Pos (mul d c) ∧ mul b c = add (mul a c) (mul d c)

      exists (mul d c)

      constructor
      · /- Pos (mul d c) -/

        apply not_zero_not_zero_mul_not_zero d c hdpos h

      · /- mul b c = add (mul a c) (mul d c) -/

        --- mul b c = add (mul a c) (mul d c)
        --- mul b c = mul (add a d) c
        rw [← mul_distr_left]

        --- mul b c = mul (add a d) c
        --- mul b c = mul b c
        rw [heq]

theorem mul_canc_right {a b c : Nt} (h : Pos c)
    (heq: mul a c = mul b c) : a = b := by

    have h_contradiction {x y : Nt}
        (heq : mul x c = mul y c) (hgt : gt x y) : False := by

        replace hgt := gt_mul_const h hgt

        obtain ⟨hge, hne⟩ := hgt

        apply hne

        exact heq

    rcases (order_trichotomy a b) with heqab | hgtab | hgtba
    · /- heqab : a = b -/
      exact heqab

    · /- hgtab : gt a b -/

      exfalso

      apply (h_contradiction (x := a) (y := b)) heq hgtab

    · /- hgtba : gt b a -/

      exfalso

      replace heq := Eq.symm heq

      apply (h_contradiction (x := b) (y := a)) heq hgtba


/- Multiplication theorems -/


def Nt.one : Nt := Nt.succ Nt.zero
def Nt.two : Nt := Nt.succ one

theorem mul_one_right (a : Nt) : mul a Nt.one = a := by
    -- mul a one = a
    -- mul a (succ zero) = a
    unfold Nt.one

    -- mul a (succ zero) = a
    -- add a (mul a zero) = a
    rw [mul_succ_right]

    -- add a (mul a zero) = a
    -- add a zero = a
    rw [mul_zero_right]

    -- add a zero = a
    -- a = a
    rw [add_zero_right]

theorem mul_one_left (a : Nt) : mul Nt.one a = a := by
    -- mul one a = a
    -- =>
    -- mul a one = a
    rw [mul_comm]

    -- mul a one = a
    -- a = a
    apply mul_one_right

theorem mul_two_left (a : Nt) : mul Nt.two a = add a a := by
    -- lhs: mul two a
    -- lhs: mul (succ one) a
    unfold Nt.two

    -- lhs: mul (succ one) a
    -- lhs: add (mul one a) a
    rw [mul_succ_left]

    -- lhs: add (mul one a) a
    -- lhs: add a a
    rw [mul_one_left]

theorem mul_two_right (a : Nt) : mul a Nt.two = add a a := by
    rw [mul_comm]
    apply mul_two_left

theorem euclidean_algorithm {n q : Nt} (hqpos : Pos q) :
    ∃ m r : Nt, n = add (mul m q) r ∧ gt q r := by

    induction n with
    | zero =>
      exists Nt.zero, Nt.zero

      constructor
      · rw [add_zero_right]
        rw [mul_zero_left]

      · constructor
        · exists q
          rw [add_zero_left]
        · exact hqpos

    | succ n ih =>

      obtain ⟨m, r, hconj⟩ := ih
      obtain ⟨heq, hgt⟩ := hconj

      by_cases hqr : q = (Nt.succ r)

      · /- hqr : q = (succ r) -/

        exists (Nt.succ m), Nt.zero

        constructor
        · rw [add_zero_right]
          -- succ n = add (mul m q) q
          rw [mul_succ_left]
          rw [hqr]
          rw [add_succ_right]
          apply succ_func
          rw [← hqr]
          apply heq
        · constructor
          · exists q
            rw [add_zero_left]
          · exact hqpos

      · /- hqr : q = (succ r) -> False -/

        have hgesucc := (gt_succ_ge q r).mp hgt

        exists m, (Nt.succ r)

        constructor
        · rw [add_succ_right]
          apply succ_func
          exact heq
        · constructor
          · exact hgesucc
          · exact hqr


/- Exponentiation definition -/

def pow (a b : Nt) : Nt :=
    match b with
    | Nt.zero => Nt.one
    | Nt.succ b' => mul a (pow a b')


/- Exponentiation properties -/


theorem pow_zero (a : Nt) : pow a Nt.zero = Nt.one := rfl

theorem pow_succ (a b : Nt) :
    pow a (Nt.succ b) = mul a (pow a b) := rfl

theorem pow_one (a : Nt) : pow a Nt.one = a := by
    -- pow a one = a
    -- pow a (succ zero) = a
    unfold Nt.one

    -- pow a (succ zero) = a
    -- mul a (pow a zero) = a
    rw [pow_succ]
 
    -- mul a (pow a zero) = a
    -- mul a one = a
    rw [pow_zero]

    -- mul a one = a
    -- a = a
    rw [mul_one_right]

theorem pow_two (a : Nt) : pow a Nt.two = mul a a := by
    -- pow a two = mul a a
    -- pow a (succ one) = mul a a
    unfold Nt.two

    -- pow a (succ one) = mul a a
    -- mul a (pow a one) = mul a a
    rw [pow_succ]

    -- mul a (pow a one) = mul a a
    -- mul a a = mul a a
    rw [pow_one]


/- Exponentiation theorems -/


theorem quadratic_identity (a b : Nt) :
    pow (add a b) Nt.two = add (pow a Nt.two)
        (add (mul Nt.two (mul a b)) (pow b Nt.two)) := by

    -- lhs: pow (add a b) two
    -- =>
    -- lhs: mul (add a b) (add a b)
    rw [pow_two]

    -- lhs: mul (add a b) (add a b)
    -- =>
    -- lhs: add (mul (add a b) a) (mul (add a b) b)
    rw [mul_distr_right]

    -- lhs: add (mul (add a b) a) (mul (add a b) b)
    -- =>
    -- lhs: add (add (mul a a) (mul b a)) (mul (add a b) b)
    rw [mul_distr_left]

    -- lhs: add (add (mul a a) (mul b a)) (mul (add a b) b)
    -- =>
    -- lhs: add (add (mul a a) (mul b a)) (add (mul a b) (mul b b))
    rw [mul_distr_left]

    -- lhs: add (add (mul a a) (mul b a)) (add (mul a b) (mul b b))
    -- lhs: add (add (mul a a) (mul a b)) (add (mul a b) (mul b b))
    conv =>
        lhs
        arg 1
        arg 2
        rw [mul_comm]

    -- lhs: add (add (mul a a) (mul a b)) (add (mul a b) (mul b b))
    -- =>
    -- lhs: add (add (add (mul a a) (mul a b)) (mul a b)) (mul b b)
    rw [add_ass]

    -- lhs: add (add (add (mul a a) (mul a b)) (mul a b)) (mul b b)
    -- =>
    -- lhs: add (add (mul a a) (add (mul a b) (mul a b))) (mul b b)
    conv =>
        lhs
        arg 1
        rw [← add_ass]

    -- lhs: add (add (mul a a) (add (mul a b) (mul a b))) (mul b b)
    -- lhs: add (add (mul a a) (mul two (mul a b))) (mul b b)
    rw [← mul_two_left]

    -- lhs: add (add (mul a a) (mul two (mul a b))) (mul b b)
    -- lhs: add (mul a a) (add (mul two (mul a b)) (mul b b))
    rw [← add_ass]

    -- lhs: add (mul a a) (add (mul two (mul a b)) (mul b b))
    -- lhs: add (pow a two) (add (mul two (mul a b)) (mul b b))
    rw [← pow_two]

    -- lhs: add (pow a two) (add (mul two (mul a b)) (mul b b))
    -- lhs: add (pow a two) (add (mul two (mul a b)) (pow b two))
    rw [← pow_two]

