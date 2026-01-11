import St.Function


/- Nt definition -/


axiom Nt : Type
axiom Nt.zero : Nt
axiom Nt.succ : Nt → Nt
axiom Nt.eq : Nt → Nt → Prop
notation:50 a " =nt " b => Nt.eq a b

axiom Nt.eq_refl {a : Nt} : a =nt a
axiom Nt.eq_symm {a b : Nt} : (a =nt b) → (b =nt a)
axiom Nt.eq_trans {a b c : Nt} : (a =nt b) → (b =nt c) → (a =nt c)
instance : Trans Nt.eq Nt.eq Nt.eq where trans := Nt.eq_trans


/- Addition definition -/


axiom Nt.add : Nt → Nt → Nt

axiom add_zero_right (n : Nt) :
    Nt.add n Nt.zero =nt n

axiom add_succ_right (a b : Nt) :
    Nt.add a (Nt.succ b) =nt Nt.succ (Nt.add a b)


/- Succ axioms -/


axiom succ_not_zero (n : Nt) : (Nt.succ n =nt Nt.zero) → False

axiom succ_inj (a b : Nt) (h : (Nt.succ a =nt Nt.succ b)) : a =nt b

axiom succ_congr {a b : Nt} : (a =nt b) → ((Nt.succ a) =nt (Nt.succ b))

axiom Nt.induction (P : Nt → Prop)
  (base : P Nt.zero)
  (step : ∀ (n : Nt), P n → P (Nt.succ n))
  : ∀ (n : Nt), P n


/- Addition properties -/


theorem add_zero_left (n : Nt) :
    Nt.add Nt.zero n =nt n := by

    let P (n : Nt) : Prop := Nt.add Nt.zero n =nt n

    /- (h_base : P Nt.zero := Nt.add Nt.zero Nt.zero =st Nt.zero) -/
    have h_base : P Nt.zero := add_zero_right Nt.zero


    /- (h_step : P n → P (Nt.succ n) 
        Nt.add Nt.zero n → Nt.add Nt.zero (Nt.succ n)) -/

    have h_step : ∀ (n : Nt),
        (Nt.add Nt.zero n =nt n) →
        (Nt.add Nt.zero (Nt.succ n) =nt (Nt.succ n)) := by

        intro n hPn

        calc
            Nt.add Nt.zero (Nt.succ n)
              =nt Nt.succ (Nt.add Nt.zero n)
                := (add_succ_right Nt.zero n)
            _ =nt (Nt.succ n)
                := succ_congr hPn


    apply (Nt.induction P h_base h_step n)


theorem add_succ_left (a b : Nt) :
    Nt.add (Nt.succ a) b =nt Nt.succ (Nt.add a b) := by

    let P (n : Nt) : Prop :=
        Nt.add (Nt.succ a) n =nt Nt.succ (Nt.add a n)

    /- (h_base : P Nt.zero :=
        Nt.add (Nt.succ a) Nt.zero =st Nt.succ (Nt.add a Nt.zero)) -/

    have h_base : P Nt.zero := by
        calc
            Nt.add (Nt.succ a) Nt.zero
               =nt Nt.succ a
                := (add_zero_right (Nt.succ a))

            _  =nt Nt.succ (Nt.add a Nt.zero)
                := succ_congr (Nt.eq_symm (add_zero_right a))

    /- (h_step : P n → P (Nt.succ n) 
        Nt.add (Nt.succ a) n =nt Nt.succ (Nt.add a n) →
        Nt.add (Nt.succ a) (Nt.succ n) =nt
            Nt.succ (Nt.add a (Nt.succ n)) -/

    have h_step : ∀ (n : Nt),
        (Nt.add (Nt.succ a) n =nt Nt.succ (Nt.add a n)) →
        (Nt.add (Nt.succ a) (Nt.succ n) =nt
            Nt.succ (Nt.add a (Nt.succ n))) := by

        intro n hPn

        calc
            Nt.add (Nt.succ a) (Nt.succ n)
              =nt Nt.succ (Nt.add (Nt.succ a) n)
                := (add_succ_right (Nt.succ a) n)

            _ =nt Nt.succ (Nt.succ (Nt.add a n))
                := succ_congr hPn

            _ =nt Nt.succ (Nt.add a (Nt.succ n))
                := (succ_congr (Nt.eq_symm (add_succ_right a n)))


    apply (Nt.induction P h_base h_step b)


theorem add_comm (a b : Nt) :
    Nt.add a b =nt Nt.add b a := by

    let P (n : Nt) : Prop := Nt.add a n =nt Nt.add n a

    /- (h_base : P Nt.zero := Nt.add a Nt.zero =nt Nt.add Nt.zero a) -/
    have h_base : P Nt.zero := by
        calc
            Nt.add a Nt.zero
               =nt a
               := (add_zero_right a)

            _  =nt Nt.add Nt.zero a
               := (Nt.eq_symm (add_zero_left a))

    /- (h_step : P n → P (Nt.succ n) 
        Nt.add a n =nt Nt.add n a →
        Nt.add a (Nt.succ n) =nt Nt.add (Nt.succ n) a -/

    have h_step : ∀ (n : Nt),
        (Nt.add a n =nt Nt.add n a) →
        (Nt.add a (Nt.succ n) =nt Nt.add (Nt.succ n) a) := by

        intro n hPn

        calc
            Nt.add a (Nt.succ n)
               =nt Nt.succ (Nt.add a n)
                := (add_succ_right a n)

            _  =nt Nt.succ (Nt.add n a)
                := succ_congr hPn

            _  =nt Nt.add (Nt.succ n) a
                := Nt.eq_symm (add_succ_left n a)

    apply (Nt.induction P h_base h_step b)

theorem add_congr_right {a b c : Nt} (h : b =nt c) :
    Nt.add a b =nt Nt.add a c := by

    let P (n : Nt) : Prop :=
        (b =nt c) → (Nt.add n b =nt Nt.add n c)

    /- (h_base : P Nt.zero :=
        (b =nt c) → (Nt.add Nt.zero b =nt Nt.add Nt.zero c) -/

    have h_base : P Nt.zero := by
        intro h

        calc
            Nt.add Nt.zero b
              =nt b := add_zero_left b
            _ =nt c := h
            _ =nt Nt.add Nt.zero c := Nt.eq_symm (add_zero_left c)

    /- (h_step : ∀ (n : Nt),
        ((b =nt c) → (Nt.add n b =nt Nt.add n c)) →
        ((b =nt c) →
        (Nt.add (Nt.succ n) b =nt Nt.add (Nt.succ n) c))) -/

    have h_step : ∀ (n : Nt), P n → P (Nt.succ n) := by

        intro n hPn h

        calc
            Nt.add (Nt.succ n) b
              =nt Nt.succ (Nt.add n b)
                := add_succ_left n b

            _ =nt Nt.succ (Nt.add n c)
                := succ_congr (hPn h)

            _ =nt Nt.add (Nt.succ n) c
                := Nt.eq_symm (add_succ_left n c)


    apply (Nt.induction P h_base h_step a)
    exact h


theorem add_congr_left {a b c : Nt} (h : b =nt c) :
    Nt.add b a =nt Nt.add c a := by

    calc
        Nt.add b a
          =nt Nt.add a b := add_comm b a
        _ =nt Nt.add a c := add_congr_right h
        _ =nt Nt.add c a := add_comm a c


theorem add_ass (a b c : Nt) :
    Nt.add a (Nt.add b c) =nt Nt.add (Nt.add a b) c := by

    let P (n : Nt) : Prop :=
        Nt.add a (Nt.add b n) =nt Nt.add (Nt.add a b) n

    /- (h_base : P Nt.zero :=
        Nt.add a (Nt.add b Nt.zero) =nt Nt.add (Nt.add a b) Nt.zero) -/

    have h_base : P Nt.zero := by
        calc
            Nt.add a (Nt.add b Nt.zero)
               =nt Nt.add a b
               := add_congr_right (add_zero_right b)

            _  =nt Nt.add (Nt.add a b) Nt.zero
               := (Nt.eq_symm (add_zero_right (Nt.add a b)))


    /- (h_step : P n → P (Nt.succ n) 
        (Nt.add a (Nt.add b n) =nt Nt.add (Nt. add a b) n) →
        (Nt.add a (Nt.add b (Nt.succ n)) =nt
            Nt.add (Nt.add a b) (Nt.succ n)) -/

    have h_step : ∀ (n : Nt),
        (Nt.add a (Nt.add b n) =nt Nt.add (Nt.add a b) n) →
        (Nt.add a (Nt.add b (Nt.succ n)) =nt
            Nt.add (Nt.add a b) (Nt.succ n)) := by

        intro n hPn

        calc
            Nt.add a (Nt.add b (Nt.succ n))
               =nt Nt.add a (Nt.succ (Nt.add b n))
                := add_congr_right (add_succ_right b n)

            _  =nt Nt.succ (Nt.add a (Nt.add b n))
                := add_succ_right a (Nt.add b n)

            _  =nt Nt.succ (Nt.add (Nt.add a b) n)
                := succ_congr hPn

            _  =nt Nt.add (Nt.add a b) (Nt.succ n)
                := Nt.eq_symm (add_succ_right (Nt.add a b) n)


    apply (Nt.induction P h_base h_step c)


theorem add_canc_left {a b c : Nt} (h : Nt.add a b =nt Nt.add a c) :
    b =nt c := by

    let P (n : Nt) : Prop :=
        (Nt.add n b =nt Nt.add n c) → (b =nt c)

    /- (h_base : P Nt.zero :=
        (Nt.add Nt.zero b =nt Nt.add Nt.zero c) → (b =nt c)  -/

    have h_base : P Nt.zero := by
        intro h

        calc
            b =nt Nt.add Nt.zero b := Nt.eq_symm (add_zero_left b)
            _ =nt Nt.add Nt.zero c := h
            _ =nt c := add_zero_left c

    /- (h_step : P n → P (Nt.succ n)
        ((Nt.add n b =nt Nt.add n c) → (b =nt c)) →
        ((Nt.add (Nt.succ n) b =nt Nt.add (Nt.succ n) c) →
        (b =nt c))) -/

    have h_step : ∀ (n : Nt), P n → P (Nt.succ n) := by

        intro n hPn h
        apply hPn
        apply succ_inj

        calc
            Nt.succ (Nt.add n b)
              =nt Nt.add (Nt.succ n) b := Nt.eq_symm (add_succ_left n b)
            _ =nt Nt.add (Nt.succ n) c := h
            _ =nt Nt.succ (Nt.add n c) := add_succ_left n c

    apply (Nt.induction P h_base h_step a)
    exact h


theorem add_canc_right {a b c : Nt} (h : Nt.add b a =nt Nt.add c a) :
    b =nt c := by

    have hcomm : Nt.add a b =nt Nt.add a c := by
        calc
            Nt.add a b
              =nt Nt.add b a := (add_comm a b)
            _ =nt Nt.add c a := h
            _ =nt Nt.add a c := (add_comm c a)

    exact (add_canc_left hcomm)


theorem ne_add_canc_left {a b c : Nt}
    (h: (Nt.add a b =nt Nt.add a c) → False) :
    (b =nt c) → False := by

    intro hbc
    apply h
    apply add_congr_right hbc

theorem ne_add_canc_right {a b c : Nt}
    (h: (Nt.add b a =nt Nt.add c a) → False) :
    (b =nt c) → False := by

    intro hbc
    apply h
    apply add_congr_left hbc


def Nt.pos (n : Nt) : Prop := (n =nt Nt.zero) → False


theorem add_pos {a b : Nt} (h : Nt.pos a) :
    Nt.pos (Nt.add a b) := by

    let P (n : Nt) : Prop := Nt.pos a → Nt.pos (Nt.add a n)

    /- (h_base : P Nt.zero := Nt.pos a → Nt.pos (Nt.add a Nt.zero)) -/
    have h_base : P Nt.zero := by

        intro hposa hposadd
        apply hposa

        calc
            a =nt Nt.add a Nt.zero := Nt.eq_symm (add_zero_right a)
            _ =nt Nt.zero := hposadd

    /- (h_step : P n → P (Nt.succ n)
        Nt.add Nt.zero n → Nt.add Nt.zero (Nt.succ n)) -/

    have h_step : ∀ (n : Nt),
        (Nt.pos a → Nt.pos (Nt.add a n)) →
        (Nt.pos a → Nt.pos (Nt.add a (Nt.succ n))) := by

        intro n hPn hposa hposaddsucc

        apply succ_not_zero (Nt.add a n)

        calc
            Nt.succ (Nt.add a n)
              =nt Nt.add a (Nt.succ n)
                := Nt.eq_symm (add_succ_right a n)

            _ =nt Nt.zero
                := hposaddsucc


    apply (Nt.induction P h_base h_step b)
    exact h


theorem add_equal_zero_then_zero {a b : Nt}
    (h : Nt.add a b =nt Nt.zero) :
    (a =nt Nt.zero) ∧ (b =nt Nt.zero) := by

    let P (n : Nt) : Prop :=
        (Nt.add a n =nt Nt.zero) → (a =nt Nt.zero) ∧ (n =nt Nt.zero)

    /- (h_base : P Nt.zero :=
        (Nt.add a Nt.zero =nt Nt.zero) →
            (a =nt Nt.zero) ∧ (Nt.zero =nt Nt.zero) -/

    have h_base : P Nt.zero := by

        intro hadda

        constructor
        · calc
            a =nt Nt.add a Nt.zero := Nt.eq_symm (add_zero_right a)
            _ =nt Nt.zero := hadda

        · apply Nt.eq_refl

    /- (h_step : P n → P (Nt.succ n)
        Nt.add Nt.zero n → Nt.add Nt.zero (Nt.succ n)) -/

    have h_step : ∀ (n : Nt),
        ((Nt.add a n =nt Nt.zero) → (a =nt Nt.zero) ∧ (n =nt Nt.zero))
        →
        ((Nt.add a (Nt.succ n) =nt Nt.zero) →
        (a =nt Nt.zero) ∧ ((Nt.succ n) =nt Nt.zero)) := by

        intro n hPn hadda

        exfalso

        apply succ_not_zero (Nt.add a n)

        calc
            Nt.succ (Nt.add a n)
              =nt (Nt.add a (Nt.succ n))
                    := Nt.eq_symm (add_succ_right a n)

            _ =nt Nt.zero := hadda


    apply (Nt.induction P h_base h_step b)
    exact h

theorem unique_ante {a : Nt} (h : Nt.pos a) :
    ∃ b : Nt, (Nt.succ b =nt a) ∧
        ∀ b' : Nt, (Nt.succ b' =nt a) → (b' =nt b) := by

    let P (n : Nt) : Prop :=
        (Nt.pos n) →
            ∃ b : Nt, (Nt.succ b =nt n) ∧
            ∀ b' : Nt, (Nt.succ b' =nt n) → (b' =nt b)

    /- (h_base : P Nt.zero :=
        (Nt.pos Nt.zero) →
            ∃ b : Nt, Nt.succ b = Nt.zero ∧
            ∀ b' : Nt, Nt.succ b' = Nt.zero → b' = b -/

    have h_base : P Nt.zero := by

        intro hpos
        exfalso
        apply hpos
        apply Nt.eq_refl

    /- (h_step : P n → P (Nt.succ n)
        ((Nt.pos n) →
            ∃ b : Nt, Nt.succ b = n ∧
            ∀ b' : Nt, Nt.succ b' = n → b' = b) ->
        ((Nt.pos (Nt.succ n)) →
            ∃ b : Nt, Nt.succ b = (succ n) ∧
            ∀ b' : Nt, Nt.succ b' = (Nt.succ n) → b' = b) -/

    have h_step : ∀ (n : Nt), P n → P (Nt.succ n) := by

        intro n hPn hpos

        exists n

        constructor
        · apply Nt.eq_refl
        · intro n' heqsucc
          apply succ_inj
          apply heqsucc


    apply (Nt.induction P h_base h_step a)
    exact h
    












