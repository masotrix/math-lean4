import St.Nt


/- Addition definition -/


axiom Nt.add : Nt → Nt → Nt

axiom Nt.add_zero_right (n : Nt) :
    Nt.add n Nt.zero =nt n

axiom Nt.add_succ_right (a b : Nt) :
    Nt.add a (Nt.succ b) =nt Nt.succ (Nt.add a b)


/- Addition properties -/


theorem Nt.add_zero_left (n : Nt) :
    Nt.add Nt.zero n =nt n := by

    let P (n : Nt) : Prop := Nt.add Nt.zero n =nt n

    have h_base : P Nt.zero := Nt.add_zero_right Nt.zero

    have h_step : ∀ (n : Nt),
        (Nt.add Nt.zero n =nt n) →
        (Nt.add Nt.zero (Nt.succ n) =nt (Nt.succ n)) := by

        intro n hPn

        calc
            Nt.add Nt.zero (Nt.succ n)
              =nt Nt.succ (Nt.add Nt.zero n)
                := Nt.add_succ_right Nt.zero n
            _ =nt (Nt.succ n)
                := Nt.succ_congr hPn


    apply (Nt.induction P h_base h_step n)


theorem Nt.add_succ_left (a b : Nt) :
    Nt.add (Nt.succ a) b =nt Nt.succ (Nt.add a b) := by

    let P (n : Nt) : Prop :=
        Nt.add (Nt.succ a) n =nt Nt.succ (Nt.add a n)

    have h_base : P Nt.zero := by
        calc
            Nt.add (Nt.succ a) Nt.zero
               =nt Nt.succ a
                := Nt.add_zero_right (Nt.succ a)

            _  =nt Nt.succ (Nt.add a Nt.zero)
                := Nt.succ_congr (Nt.eq_symm (Nt.add_zero_right a))

    have h_step : ∀ (n : Nt),
        (Nt.add (Nt.succ a) n =nt Nt.succ (Nt.add a n)) →
        (Nt.add (Nt.succ a) (Nt.succ n) =nt
            Nt.succ (Nt.add a (Nt.succ n))) := by

        intro n hPn

        calc
            Nt.add (Nt.succ a) (Nt.succ n)
              =nt Nt.succ (Nt.add (Nt.succ a) n)
                := Nt.add_succ_right (Nt.succ a) n

            _ =nt Nt.succ (Nt.succ (Nt.add a n))
                := Nt.succ_congr hPn

            _ =nt Nt.succ (Nt.add a (Nt.succ n))
                := Nt.succ_congr (Nt.eq_symm (Nt.add_succ_right a n))


    apply (Nt.induction P h_base h_step b)


theorem Nt.add_comm (a b : Nt) :
    Nt.add a b =nt Nt.add b a := by

    let P (n : Nt) : Prop := Nt.add a n =nt Nt.add n a

    have h_base : P Nt.zero := by
        calc
            Nt.add a Nt.zero
               =nt a
               := Nt.add_zero_right a

            _  =nt Nt.add Nt.zero a
               := Nt.eq_symm (Nt.add_zero_left a)

    have h_step : ∀ (n : Nt),
        (Nt.add a n =nt Nt.add n a) →
        (Nt.add a (Nt.succ n) =nt Nt.add (Nt.succ n) a) := by

        intro n hPn

        calc
            Nt.add a (Nt.succ n)
               =nt Nt.succ (Nt.add a n)
                := Nt.add_succ_right a n

            _  =nt Nt.succ (Nt.add n a)
                := Nt.succ_congr hPn

            _  =nt Nt.add (Nt.succ n) a
                := Nt.eq_symm (Nt.add_succ_left n a)

    apply (Nt.induction P h_base h_step b)

theorem Nt.add_congr_right {a b c : Nt} (h : b =nt c) :
    Nt.add a b =nt Nt.add a c := by

    let P (n : Nt) : Prop :=
        (b =nt c) → (Nt.add n b =nt Nt.add n c)

    have h_base : P Nt.zero := by
        intro h

        calc
            Nt.add Nt.zero b
              =nt b := Nt.add_zero_left b
            _ =nt c := h
            _ =nt Nt.add Nt.zero c := Nt.eq_symm (Nt.add_zero_left c)

    have h_step : ∀ (n : Nt), P n → P (Nt.succ n) := by

        intro n hPn h

        calc
            Nt.add (Nt.succ n) b
              =nt Nt.succ (Nt.add n b)
                := Nt.add_succ_left n b

            _ =nt Nt.succ (Nt.add n c)
                := Nt.succ_congr (hPn h)

            _ =nt Nt.add (Nt.succ n) c
                := Nt.eq_symm (Nt.add_succ_left n c)


    apply (Nt.induction P h_base h_step a)
    exact h


theorem Nt.add_congr_left {a b c : Nt} (h : b =nt c) :
    Nt.add b a =nt Nt.add c a := by

    calc
        Nt.add b a
          =nt Nt.add a b := Nt.add_comm b a
        _ =nt Nt.add a c := Nt.add_congr_right h
        _ =nt Nt.add c a := Nt.add_comm a c


theorem Nt.add_ass (a b c : Nt) :
    Nt.add a (Nt.add b c) =nt Nt.add (Nt.add a b) c := by

    let P (n : Nt) : Prop :=
        Nt.add a (Nt.add b n) =nt Nt.add (Nt.add a b) n

    have h_base : P Nt.zero := by
        calc
            Nt.add a (Nt.add b Nt.zero)
               =nt Nt.add a b
               := Nt.add_congr_right (Nt.add_zero_right b)

            _  =nt Nt.add (Nt.add a b) Nt.zero
               := (Nt.eq_symm (Nt.add_zero_right (Nt.add a b)))

    have h_step : ∀ (n : Nt),
        (Nt.add a (Nt.add b n) =nt Nt.add (Nt.add a b) n) →
        (Nt.add a (Nt.add b (Nt.succ n)) =nt
            Nt.add (Nt.add a b) (Nt.succ n)) := by

        intro n hPn

        calc
            Nt.add a (Nt.add b (Nt.succ n))
               =nt Nt.add a (Nt.succ (Nt.add b n))
                := Nt.add_congr_right (Nt.add_succ_right b n)

            _  =nt Nt.succ (Nt.add a (Nt.add b n))
                := Nt.add_succ_right a (Nt.add b n)

            _  =nt Nt.succ (Nt.add (Nt.add a b) n)
                := Nt.succ_congr hPn

            _  =nt Nt.add (Nt.add a b) (Nt.succ n)
                := Nt.eq_symm (Nt.add_succ_right (Nt.add a b) n)


    apply (Nt.induction P h_base h_step c)


theorem Nt.add_canc_left {b c : Nt} (a : Nt)
    (h : Nt.add a b =nt Nt.add a c) : b =nt c := by

    let P (n : Nt) : Prop :=
        (Nt.add n b =nt Nt.add n c) → (b =nt c)

    have h_base : P Nt.zero := by
        intro h

        calc
            b =nt Nt.add Nt.zero b := Nt.eq_symm (Nt.add_zero_left b)
            _ =nt Nt.add Nt.zero c := h
            _ =nt c := Nt.add_zero_left c

    have h_step : ∀ (n : Nt), P n → P (Nt.succ n) := by

        intro n hPn h
        apply hPn
        apply succ_inj

        calc
            Nt.succ (Nt.add n b)
              =nt Nt.add (Nt.succ n) b := Nt.eq_symm (add_succ_left n b)
            _ =nt Nt.add (Nt.succ n) c := h
            _ =nt Nt.succ (Nt.add n c) := Nt.add_succ_left n c

    apply (Nt.induction P h_base h_step a)
    exact h


theorem Nt.add_canc_right {a b c : Nt}
    (h : Nt.add b a =nt Nt.add c a) : b =nt c := by

    have hcomm : Nt.add a b =nt Nt.add a c := by
        calc
            Nt.add a b
              =nt Nt.add b a := (Nt.add_comm a b)
            _ =nt Nt.add c a := h
            _ =nt Nt.add a c := (Nt.add_comm c a)

    exact (add_canc_left a hcomm)


theorem Nt.ne_add_canc_left {a b c : Nt}
    (h: (Nt.add a b =nt Nt.add a c) → False) :
    (b =nt c) → False := by

    intro hbc
    apply h
    apply Nt.add_congr_right hbc

theorem Nt.ne_add_canc_right {a b c : Nt}
    (h: (Nt.add b a =nt Nt.add c a) → False) :
    (b =nt c) → False := by

    intro hbc
    apply h
    apply Nt.add_congr_left hbc


def Nt.pos (n : Nt) : Prop := (n =nt Nt.zero) → False

theorem Nt.add_pos {a b : Nt} (h : Nt.pos a) :
    Nt.pos (Nt.add a b) := by

    let P (n : Nt) : Prop := Nt.pos a → Nt.pos (Nt.add a n)

    have h_base : P Nt.zero := by

        intro hposa hposadd
        apply hposa

        calc
            a =nt Nt.add a Nt.zero := Nt.eq_symm (Nt.add_zero_right a)
            _ =nt Nt.zero := hposadd

    have h_step : ∀ (n : Nt),
        (Nt.pos a → Nt.pos (Nt.add a n)) →
        (Nt.pos a → Nt.pos (Nt.add a (Nt.succ n))) := by

        intro n hPn hposa hposaddsucc

        apply Nt.succ_ne_zero (Nt.add a n)

        calc
            Nt.succ (Nt.add a n)
              =nt Nt.add a (Nt.succ n)
                := Nt.eq_symm (add_succ_right a n)

            _ =nt Nt.zero
                := hposaddsucc


    apply (Nt.induction P h_base h_step b)
    exact h


theorem Nt.add_equal_zero_then_zero {a b : Nt}
    (h : Nt.add a b =nt Nt.zero) :
    (a =nt Nt.zero) ∧ (b =nt Nt.zero) := by

    let P (n : Nt) : Prop :=
        (Nt.add a n =nt Nt.zero) → (a =nt Nt.zero) ∧ (n =nt Nt.zero)

    have h_base : P Nt.zero := by

        intro hadda

        constructor
        · calc
            a =nt Nt.add a Nt.zero := Nt.eq_symm (Nt.add_zero_right a)
            _ =nt Nt.zero := hadda

        · apply Nt.eq_rfl

    have h_step : ∀ (n : Nt),
        ((Nt.add a n =nt Nt.zero) → (a =nt Nt.zero) ∧ (n =nt Nt.zero))
        →
        ((Nt.add a (Nt.succ n) =nt Nt.zero) →
        (a =nt Nt.zero) ∧ ((Nt.succ n) =nt Nt.zero)) := by

        intro n hPn hadda

        exfalso

        apply Nt.succ_ne_zero (Nt.add a n)

        calc
            Nt.succ (Nt.add a n)
              =nt (Nt.add a (Nt.succ n))
                    := Nt.eq_symm (Nt.add_succ_right a n)

            _ =nt Nt.zero := hadda


    apply (Nt.induction P h_base h_step b)
    exact h


theorem Nt.unique_ante {a : Nt} (h : Nt.pos a) :
    ∃ b : Nt, (Nt.succ b =nt a) ∧
        ∀ b' : Nt, (Nt.succ b' =nt a) → (b' =nt b) := by

    let P (n : Nt) : Prop :=
        (Nt.pos n) →
            ∃ b : Nt, (Nt.succ b =nt n) ∧
            ∀ b' : Nt, (Nt.succ b' =nt n) → (b' =nt b)

    have h_base : P Nt.zero := by

        intro hpos
        exfalso
        apply hpos
        apply Nt.eq_rfl

    have h_step : ∀ (n : Nt), P n → P (Nt.succ n) := by

        intro n hPn hpos

        exists n

        constructor
        · apply Nt.eq_rfl
        · intro n' heqsucc
          apply Nt.succ_inj
          apply heqsucc


    apply (Nt.induction P h_base h_step a)
    exact h












