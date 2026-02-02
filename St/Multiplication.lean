import St.Order


/- Multiplication definition -/


axiom Nt.mul : Nt → Nt → Nt

axiom Nt.mul_zero_right (a : Nt) :
    Nt.mul a Nt.zero =nt Nt.zero

axiom Nt.mul_succ_right (a b : Nt) :
    Nt.mul a (Nt.succ b) =nt Nt.add a (Nt.mul a b)


/- Multiplication properties -/


theorem Nt.mul_zero_left (a : Nt) : Nt.mul Nt.zero a =nt Nt.zero := by

    let P (n : Nt) : Prop := Nt.mul Nt.zero n =nt Nt.zero

    have h_base : P Nt.zero := by
        exact Nt.mul_zero_right Nt.zero

    have h_step : ∀ n : Nt, P n → P (Nt.succ n) := by
        intro n hPn

        calc
            (Nt.mul Nt.zero (Nt.succ n))
                =nt (Nt.add Nt.zero (Nt.mul Nt.zero n))
                    := Nt.mul_succ_right Nt.zero n

            _   =nt Nt.mul Nt.zero n
                    := Nt.add_zero_left (Nt.mul Nt.zero n)

            _   =nt Nt.zero
                    := hPn

    apply Nt.induction P h_base h_step a


theorem Nt.mul_succ_left (a b : Nt) :
    Nt.mul (Nt.succ a) b =nt Nt.add (Nt.mul a b) b := by

    let P (n m : Nt) : Prop :=
        Nt.mul (Nt.succ n) m =nt Nt.add (Nt.mul n m) m

    have h_base : ∀ (m : Nt), P Nt.zero m := by

        let P_base (m : Nt) : Prop := P Nt.zero m

        have h_base_base : P Nt.zero Nt.zero := by

            calc
                (Nt.mul (Nt.succ Nt.zero) Nt.zero)
                    =nt Nt.zero
                        := Nt.mul_zero_right (Nt.succ Nt.zero)
                _   =nt Nt.add Nt.zero Nt.zero
                        := Nt.eq_symm (Nt.add_zero_right Nt.zero)

                _   =nt Nt.add (Nt.mul Nt.zero Nt.zero) Nt.zero
                        := Nt.add_congr_left
                            (Nt.eq_symm (Nt.mul_zero_right Nt.zero))

        have h_base_step :
            ∀ (m : Nt), P Nt.zero m → P Nt.zero (Nt.succ m) := by

            intro m hPm

            calc
                (Nt.mul (Nt.succ Nt.zero) (Nt.succ m))
                    =nt (Nt.add (Nt.succ Nt.zero)
                            (Nt.mul (Nt.succ Nt.zero) m))
                        := Nt.mul_succ_right (Nt.succ Nt.zero) m

                _   =nt (Nt.add (Nt.succ Nt.zero)
                            (Nt.add (Nt.mul Nt.zero m) m))
                        := Nt.add_congr_right hPm

                _   =nt (Nt.succ (Nt.add Nt.zero
                                (Nt.add (Nt.mul Nt.zero m) m)))
                        := Nt.add_succ_left Nt.zero
                            (Nt.add (Nt.mul Nt.zero m) m)

                _   =nt (Nt.add Nt.zero
                            (Nt.succ (Nt.add (Nt.mul Nt.zero m) m)))
                        := Nt.eq_symm (Nt.add_succ_right Nt.zero
                            (Nt.add (Nt.mul Nt.zero m) m))

                _   =nt (Nt.add Nt.zero
                            (Nt.add (Nt.mul Nt.zero m) (Nt.succ m)))
                        := Nt.add_congr_right (Nt.eq_symm
                            (Nt.add_succ_right (Nt.mul Nt.zero m) m))

                _   =nt (Nt.add (Nt.add Nt.zero (Nt.mul Nt.zero m))
                            (Nt.succ m))
                        := Nt.add_ass Nt.zero
                            (Nt.mul Nt.zero m) (Nt.succ m)

                _   =nt (Nt.add (Nt.mul Nt.zero (Nt.succ m))
                            (Nt.succ m))
                        := Nt.add_congr_left (Nt.eq_symm
                            (Nt.mul_succ_right Nt.zero m))

        intro m

        apply Nt.induction P_base h_base_base h_base_step m


    have h_step : ∀ (m : Nt), ∀ (n : Nt), P n m → P (Nt.succ n) m := by

        let P_step (m : Nt) : Prop :=
            ∀ (n : Nt), P n m → P (Nt.succ n) m

        have h_step_base :
            ∀ (n : Nt), P n Nt.zero → P (Nt.succ n) Nt.zero := by

            intro n hPn

            calc
                Nt.mul (Nt.succ (Nt.succ n)) Nt.zero
                    =nt Nt.zero
                        := Nt.mul_zero_right (Nt.succ (Nt.succ n))

                _   =nt (Nt.mul (Nt.succ n) Nt.zero)
                        := Nt.eq_symm (Nt.mul_zero_right (Nt.succ n))

                _   =nt Nt.add (Nt.mul (Nt.succ n) Nt.zero) Nt.zero
                        := Nt.eq_symm (Nt.add_zero_right 
                            (Nt.mul (Nt.succ n) Nt.zero))


        have h_step_step :
            ∀ (m : Nt),
                (∀ (n : Nt), P n m → P (Nt.succ n) m)
                →
                (∀ (n : Nt),  P n (Nt.succ m) →
                    P (Nt.succ n) (Nt.succ m))
            := by

            intro m h_step_n n hPnsuccm

            have hPsuccnm : P (Nt.succ n) m := by
                apply h_step_n n

                apply Nt.add_canc_left (Nt.succ n)

                calc
                    (Nt.add (Nt.succ n) (Nt.mul (Nt.succ n) m))
                        =nt (Nt.mul (Nt.succ n) (Nt.succ m))
                            := Nt.eq_symm
                                (Nt.mul_succ_right (Nt.succ n) m)

                    _   =nt (Nt.add (Nt.mul n (Nt.succ m)) (Nt.succ m))
                            := hPnsuccm

                    _   =nt (Nt.add (Nt.add n (Nt.mul n m)) (Nt.succ m))
                            := Nt.add_congr_left (Nt.mul_succ_right n m)

                    _   =nt (Nt.add n (Nt.add (Nt.mul n m) (Nt.succ m)))
                            := Nt.eq_symm
                                (Nt.add_ass n (Nt.mul n m) (Nt.succ m))

                    _   =nt (Nt.add n (Nt.succ (Nt.add (Nt.mul n m) m)))
                            := Nt.add_congr_right
                                (Nt.add_succ_right (Nt.mul n m) m)

                    _   =nt (Nt.succ (Nt.add n (Nt.add (Nt.mul n m) m)))
                            := (Nt.add_succ_right n
                                (Nt.add (Nt.mul n m) m))

                    _   =nt (Nt.add (Nt.succ n) (Nt.add (Nt.mul n m) m))
                            := (Nt.eq_symm (Nt.add_succ_left n
                                (Nt.add (Nt.mul n m) m)))


            calc
                (Nt.mul (Nt.succ (Nt.succ n)) (Nt.succ m))
                    =nt (Nt.add (Nt.succ (Nt.succ n))
                                (Nt.mul (Nt.succ (Nt.succ n)) m))
                        := Nt.mul_succ_right (Nt.succ (Nt.succ n)) m

                _   =nt (Nt.add (Nt.succ (Nt.succ n))
                                (Nt.add (Nt.mul (Nt.succ n) m) m))
                        := Nt.add_congr_right hPsuccnm

                _   =nt (Nt.succ (Nt.add (Nt.succ n)
                                (Nt.add (Nt.mul (Nt.succ n) m) m)))
                        := Nt.add_succ_left (Nt.succ n)
                            (Nt.add (Nt.mul (Nt.succ n) m) m)

                _   =nt (Nt.add (Nt.succ n)
                        (Nt.succ (Nt.add (Nt.mul (Nt.succ n) m) m)))
                        := Nt.eq_symm (Nt.add_succ_right (Nt.succ n)
                                (Nt.add (Nt.mul (Nt.succ n) m) m))

                _   =nt (Nt.add (Nt.succ n)
                        (Nt.add (Nt.mul (Nt.succ n) m) (Nt.succ m)))
                        := Nt.add_congr_right (Nt.eq_symm (
                            Nt.add_succ_right (Nt.mul (Nt.succ n) m) m))

                _   =nt (Nt.add (Nt.add (Nt.succ n)
                            (Nt.mul (Nt.succ n) m)) (Nt.succ m))
                        := Nt.add_ass (Nt.succ n)
                                (Nt.mul (Nt.succ n) m) (Nt.succ m)

                _   =nt (Nt.add (Nt.mul (Nt.succ n) (Nt.succ m))
                            (Nt.succ m))
                        := Nt.add_congr_left (Nt.eq_symm
                            (Nt.mul_succ_right (Nt.succ n) m))


        intro m
        apply Nt.induction P_step h_step_base h_step_step m

    let P_b (a : Nt) : Prop := P a b

    apply Nt.induction P_b (h_base b) (h_step b) a


theorem Nt.mul_comm (a b : Nt) : Nt.mul a b =nt Nt.mul b a := by

    let P (n m : Nt) : Prop := Nt.mul n m =nt Nt.mul m n

    have h_base : ∀ (m : Nt), P Nt.zero m := by

        let P_base (m : Nt) : Prop := P Nt.zero m

        have h_base_base : P Nt.zero Nt.zero := by

            apply Nt.eq_rfl

        have h_base_step :
            ∀ (m : Nt), P Nt.zero m → P Nt.zero (Nt.succ m) := by

            intro m hPm

            calc
                (Nt.mul Nt.zero (Nt.succ m))
                    =nt Nt.zero
                        := Nt.mul_zero_left (Nt.succ m)

                _   =nt Nt.mul (Nt.succ m) Nt.zero
                        := Nt.eq_symm (Nt.mul_zero_right (Nt.succ m))

        intro m
        apply Nt.induction P_base h_base_base h_base_step m

    have h_step : ∀ (m : Nt), ∀ (n : Nt),
        P n m → P (Nt.succ n) m := by

        let P_step (m : Nt) : Prop :=
            ∀ (n : Nt), P n m → P (Nt.succ n) m

        have h_step_base :
            ∀ (n : Nt), P n Nt.zero → P (Nt.succ n) Nt.zero := by

            intro n hPn

            calc
                (Nt.mul (Nt.succ n) Nt.zero)
                    =nt Nt.zero
                        := Nt.mul_zero_right (Nt.succ n)

                _   =nt (Nt.mul Nt.zero (Nt.succ n))
                        := Nt.eq_symm (Nt.mul_zero_left (Nt.succ n))

        have h_step_step :
            ∀ (m : Nt),
                (∀ (n : Nt), P n m → P (Nt.succ n) m)
                →
                (∀ (n : Nt),  P n (Nt.succ m) →
                    P (Nt.succ n) (Nt.succ m))
            := by

            intro m h_step_n n hPnsuccm

            calc
                (Nt.mul (Nt.succ n) (Nt.succ m))
                    =nt Nt.add (Nt.mul n (Nt.succ m)) (Nt.succ m)
                        := Nt.mul_succ_left n (Nt.succ m)

                _   =nt Nt.add (Nt.succ m) (Nt.mul n (Nt.succ m))
                        := Nt.add_comm
                            (Nt.mul n (Nt.succ m)) (Nt.succ m)

                _   =nt Nt.add (Nt.succ m) (Nt.mul (Nt.succ m) n)
                        := Nt.add_congr_right hPnsuccm

                _   =nt Nt.mul (Nt.succ m) (Nt.succ n)
                        := Nt.eq_symm (Nt.mul_succ_right (Nt.succ m) n)

        intro m
        apply Nt.induction P_step h_step_base h_step_step m

    let P_b (a : Nt) : Prop := P a b

    apply Nt.induction P_b (h_base b) (h_step b) a


theorem Nt.mul_congr_right {a b c : Nt} (h : b =nt c) :
    Nt.mul a b =nt Nt.mul a c := by

    let P (n : Nt) : Prop :=
        (b =nt c) → (Nt.mul n b =nt Nt.mul n c)

    have h_base : P Nt.zero := by

        intro hbeqc

        calc
            (Nt.mul Nt.zero b)
                =nt Nt.zero
                    := Nt.mul_zero_left b

            _   =nt (Nt.mul Nt.zero c)
                    := Nt.eq_symm (Nt.mul_zero_left c)

    have h_step : ∀ (n : Nt), P n → P (Nt.succ n) := by

        intro n hPn hbeqc

        calc
            (Nt.mul (Nt.succ n) b)
                =nt (Nt.add (Nt.mul n b) b)
                    := Nt.mul_succ_left n b

            _   =nt (Nt.add (Nt.mul n c) b)
                    := Nt.add_congr_left (hPn hbeqc)

            _   =nt (Nt.add (Nt.mul n c) c)
                    := Nt.add_congr_right hbeqc

            _   =nt (Nt.mul (Nt.succ n) c)
                    := Nt.eq_symm (Nt.mul_succ_left n c)

    let P_a := Nt.induction P h_base h_step a
    apply P_a h


theorem Nt.mul_congr_left {a b c : Nt} (h : b =nt c) :
    Nt.mul b a =nt Nt.mul c a := by

    calc
        (Nt.mul b a)
            =nt (Nt.mul a b)
                := Nt.mul_comm b a

        _   =nt (Nt.mul a c)
                := Nt.mul_congr_right h

        _   =nt (Nt.mul c a)
                := Nt.mul_comm a c


theorem mul_zero_iff_factors_zero {a b : Nt} :
    (Nt.mul a b =nt Nt.zero) ↔ (a =nt Nt.zero) ∨ (b =nt Nt.zero) := by

    constructor
    · intro habeqzero

      by_cases haeqzero : a =nt Nt.zero
      · left
        exact haeqzero

      · by_cases hbeqzero : b =nt Nt.zero
        · right
          exact hbeqzero

        · have ⟨c, haeqsuccc, huniquec⟩ := Nt.unique_ante haeqzero
          have ⟨d, hbeqsuccd, huniqued⟩ := Nt.unique_ante hbeqzero

          have hsucczero :
            Nt.succ (Nt.add c (Nt.mul (Nt.succ c) d)) =nt Nt.zero := by

            calc
                (Nt.succ (Nt.add c (Nt.mul (Nt.succ c) d)))
                    =nt (Nt.add (Nt.succ c) (Nt.mul (Nt.succ c) d))
                        := Nt.eq_symm (Nt.add_succ_left c
                            (Nt.mul (Nt.succ c) d))

                _   =nt (Nt.mul (Nt.succ c) (Nt.succ d))
                        := Nt.eq_symm (Nt.mul_succ_right (Nt.succ c) d)

                _   =nt (Nt.mul a (Nt.succ d))
                        := Nt.mul_congr_left haeqsuccc

                _   =nt (Nt.mul a b)
                        := Nt.mul_congr_right hbeqsuccd

                _   =nt Nt.zero
                        := habeqzero

          exfalso
          apply Nt.succ_ne_zero
            (Nt.add c (Nt.mul (Nt.succ c) d)) hsucczero


    · intro habzero
      rcases habzero with haeqzero | hbeqzero

      · calc
            (Nt.mul a b)
                =nt (Nt.mul Nt.zero b)
                    := Nt.mul_congr_left haeqzero

            _   =nt Nt.zero
                    := Nt.mul_zero_left b

      · calc
            (Nt.mul a b)
                =nt (Nt.mul a Nt.zero)
                    := Nt.mul_congr_right hbeqzero

            _   =nt Nt.zero
                    := Nt.mul_zero_right a

theorem Nt.mul_not_zero_if_factors_not_zero (a b : Nt)
    (hanezero : (a =nt Nt.zero) → False)
    (hbnezero : (b =nt Nt.zero) → False) :

    ((Nt.mul a b =nt Nt.zero) → False) := by

    intro habeqzero

    have haeqzeroANDbeqzero := mul_zero_iff_factors_zero.mp habeqzero

    rcases haeqzeroANDbeqzero with haeqzero | hbeqzero
    · apply hanezero
      exact haeqzero
    · apply hbnezero
      exact hbeqzero


theorem Nt.mul_distr_right (a b c : Nt) :
    Nt.mul a (Nt.add b c) =nt Nt.add (Nt.mul a b) (Nt.mul a c) := by

    let P (n : Nt) : Prop := Nt.mul n (Nt.add b c) =nt
        Nt.add (Nt.mul n b) (Nt.mul n c)

    have h_base : P Nt.zero := by

        calc
            (Nt.mul Nt.zero (Nt.add b c))
                =nt Nt.zero
                    := Nt.mul_zero_left (Nt.add b c)

            _   =nt Nt.add Nt.zero Nt.zero
                    := Nt.eq_symm (Nt.add_zero_right Nt.zero)

            _   =nt Nt.add (Nt.mul Nt.zero b) Nt.zero
                    := Nt.add_congr_left (
                        Nt.eq_symm (Nt.mul_zero_left b))

            _   =nt Nt.add (Nt.mul Nt.zero b) (Nt.mul Nt.zero c)
                    := Nt.add_congr_right (
                        Nt.eq_symm (Nt.mul_zero_left c))

    have h_step : ∀ (n : Nt), P n → P (Nt.succ n) := by

        intro n hPn

        calc
            (Nt.mul (Nt.succ n) (Nt.add b c))
                =nt (Nt.add (Nt.mul n (Nt.add b c)) (Nt.add b c))
                    := Nt.mul_succ_left n (Nt.add b c)

            _   =nt (Nt.add (Nt.add (Nt.mul n b) (Nt.mul n c))
                        (Nt.add b c))
                    := Nt.add_congr_left hPn

            _   =nt (Nt.add (Nt.mul n b)
                        (Nt.add (Nt.mul n c) (Nt.add b c)))
                    := Nt.eq_symm (Nt.add_ass 
                        (Nt.mul n b) (Nt.mul n c) (Nt.add b c))

            _   =nt (Nt.add (Nt.mul n b)
                        (Nt.add (Nt.mul n c) (Nt.add c b)))
                    := Nt.add_congr_right (Nt.add_congr_right (
                        Nt.add_comm b c))

            _   =nt (Nt.add (Nt.mul n b)
                        (Nt.add (Nt.add (Nt.mul n c) c) b))
                    := Nt.add_congr_right (Nt.add_ass (Nt.mul n c) c b)

            _   =nt (Nt.add (Nt.mul n b)
                        (Nt.add (Nt.mul (Nt.succ n) c) b))
                    := Nt.add_congr_right (Nt.add_congr_left (
                        Nt.eq_symm (Nt.mul_succ_left n c)))

            _   =nt (Nt.add (Nt.mul n b)
                        (Nt.add b (Nt.mul (Nt.succ n) c)))
                    := Nt.add_congr_right (
                        Nt.add_comm (Nt.mul (Nt.succ n) c) b)

            _   =nt (Nt.add (Nt.add (Nt.mul n b) b)
                        (Nt.mul (Nt.succ n) c))
                    := Nt.add_ass (Nt.mul n b) b (Nt.mul (Nt.succ n) c)

            _   =nt (Nt.add (Nt.mul (Nt.succ n) b)
                        (Nt.mul (Nt.succ n) c))
                    := Nt.add_congr_left (Nt.eq_symm (
                        Nt.mul_succ_left n b))

    apply Nt.induction P h_base h_step a


theorem Nt.mul_distr_left (a b c : Nt) :
    Nt.mul (Nt.add b c) a =nt Nt.add (Nt.mul b a) (Nt.mul c a) := by

    calc
        (Nt.mul (Nt.add b c) a)
            =nt Nt.mul a (Nt.add b c)
                := Nt.mul_comm (Nt.add b c) a

        _   =nt Nt.add (Nt.mul a b) (Nt.mul a c)
                := Nt.mul_distr_right a b c

        _   =nt Nt.add (Nt.mul b a) (Nt.mul a c)
                := Nt.add_congr_left (Nt.mul_comm a b)

        _   =nt Nt.add (Nt.mul b a) (Nt.mul c a)
                := Nt.add_congr_right (Nt.mul_comm a c)


theorem Nt.mul_ass (a b c : Nt) :
    Nt.mul (Nt.mul a b) c =nt Nt.mul a (Nt.mul b c) := by

    let P (n : Nt) : Prop :=
        Nt.mul (Nt.mul a b) n =nt Nt.mul a (Nt.mul b n)

    have h_base : P Nt.zero := by

        calc
            (Nt.mul (Nt.mul a b) Nt.zero)
                =nt Nt.zero
                    := Nt.mul_zero_right (Nt.mul a b)

            _   =nt Nt.mul a Nt.zero
                    := Nt.eq_symm (Nt.mul_zero_right a)

            _   =nt Nt.mul a (Nt.mul b Nt.zero)
                    := Nt.mul_congr_right (Nt.eq_symm (
                        Nt.mul_zero_right b))

    have h_step : ∀ (n : Nt), P n → P (Nt.succ n) := by
        intro n hPn

        calc
            (Nt.mul (Nt.mul a b) (Nt.succ n))
                =nt (Nt.add (Nt.mul a b) (Nt.mul (Nt.mul a b) n))
                    := Nt.mul_succ_right (Nt.mul a b) n

            _   =nt (Nt.add (Nt.mul a b) (Nt.mul a (Nt.mul b n) ))
                    := Nt.add_congr_right hPn

            _   =nt (Nt.mul a (Nt.add b (Nt.mul b n)))
                    := Nt.eq_symm (Nt.mul_distr_right a b (Nt.mul b n))

            _   =nt (Nt.mul a (Nt.mul b (Nt.succ n)))
                    := Nt.mul_congr_right (Nt.eq_symm (
                        Nt.mul_succ_right b n))

    apply Nt.induction P h_base h_step c


theorem Nt.gt_mul_const (a b c : Nt)
    (hcpos : Nt.pos c) (hbgta : Nt.gt b a) :
    Nt.gt (Nt.mul b c) (Nt.mul a c) := by

    rcases (Nt.gt_exists_pos b a).mp hbgta with ⟨d, hdpos, hbeqad⟩

    apply (Nt.gt_exists_pos (Nt.mul b c) (Nt.mul a c)).mpr

    exists (Nt.mul d c)

    constructor
    · apply Nt.mul_not_zero_if_factors_not_zero d c hdpos hcpos
    · calc
        (Nt.mul b c)
            =nt Nt.mul (Nt.add a d) c
                := Nt.mul_congr_left hbeqad

        _   =nt Nt.add (Nt.mul a c) (Nt.mul d c)
                := Nt.mul_distr_left c a d


theorem Nt.mul_canc_right {a b c : Nt}
    (hcpos : Nt.pos c) (haceqbc : (Nt.mul a c) =nt (Nt.mul b c)) :
    a =nt b := by

    have h_contradiction (x y : Nt)
        (hxceqyc : Nt.mul x c =nt Nt.mul y c)
        (hxgty : Nt.gt x y) : False := by

        have hxcgtyc : Nt.gt (Nt.mul x c) (Nt.mul y c) :=
            Nt.gt_mul_const y x c hcpos hxgty

        rcases hxcgtyc with ⟨hxcgeyc, hxcneyc⟩

        apply hxcneyc
        exact hxceqyc

    rcases (Nt.order_trichotomy a b) with haeqb | hagtb | hbgta
    · exact haeqb

    · exfalso
      apply (h_contradiction a b haceqbc hagtb)

    · exfalso
      have hbceqac := Nt.eq_symm haceqbc
      apply (h_contradiction b a hbceqac hbgta)


/- Multiplication theorems -/


noncomputable def Nt.one : Nt := (Nt.succ Nt.zero)
noncomputable def Nt.two : Nt := (Nt.succ Nt.one)

theorem Nt.mul_one_right (a : Nt) : (Nt.mul a Nt.one) =nt a := by
    unfold Nt.one

    calc
        (Nt.mul a (Nt.succ Nt.zero))
            =nt (Nt.add a (Nt.mul a Nt.zero))
                := Nt.mul_succ_right a Nt.zero

        _   =nt (Nt.add a Nt.zero)
                := Nt.add_congr_right (Nt.mul_zero_right a)

        _   =nt a
                := Nt.add_zero_right a

theorem Nt.mul_one_left (a : Nt) : (Nt.mul Nt.one a) =nt a := by
    calc
        (Nt.mul Nt.one a)
            =nt (Nt.mul a Nt.one)
                := Nt.mul_comm Nt.one a

        _   =nt a
                := Nt.mul_one_right a

theorem Nt.mul_two_right (a : Nt) :
    (Nt.mul a Nt.two) =nt (Nt.add a a) := by

    unfold Nt.two

    calc
        (Nt.mul a (Nt.succ Nt.one))
            =nt Nt.add a (Nt.mul a Nt.one)
                := Nt.mul_succ_right a Nt.one

        _   =nt Nt.add a a
                := Nt.add_congr_right (Nt.mul_one_right a)


theorem Nt.mul_two_left (a : Nt) :
    (Nt.mul Nt.two a) =nt (Nt.add a a) := by

    calc
        (Nt.mul Nt.two a)
            =nt (Nt.mul a Nt.two)
                := Nt.mul_comm Nt.two a

        _   =nt (Nt.add a a)
                := Nt.mul_two_right a


theorem euclidean_algorithm (n q : Nt) (hqpos : Nt.pos q) :
    ∃ m r : Nt, (n =nt Nt.add (Nt.mul m q) r) ∧ (Nt.gt q r) := by

    let P (a : Nt) : Prop :=
        ∃ m r : Nt, (a =nt Nt.add (Nt.mul m q) r) ∧ (Nt.gt q r)

    have h_base : P Nt.zero := by
        exists Nt.zero, Nt.zero

        constructor
        · calc
            Nt.zero
                =nt Nt.add Nt.zero Nt.zero
                    := Nt.eq_symm (Nt.add_zero_right Nt.zero)

            _   =nt Nt.add (Nt.mul Nt.zero q) Nt.zero
                    := Nt.add_congr_left (Nt.eq_symm (
                        Nt.mul_zero_left q))
        · constructor
          · exists q
            apply (Nt.eq_symm (Nt.add_zero_left q))
          · exact hqpos

    have h_step : ∀ a : Nt, P a → P (Nt.succ a) := by

        intro a hPa

        rcases hPa with ⟨m, r, hconj⟩
        rcases hconj with ⟨haeqmqr, hqgtr⟩

        by_cases hqeqsuccr : q =nt (Nt.succ r)
        · exists (Nt.succ m), Nt.zero

          constructor
          · have hsuccaeqsuccmqr := Nt.succ_congr haeqmqr

            calc
                (Nt.succ a)
                    =nt Nt.succ (Nt.add (Nt.mul m q) r)
                        := hsuccaeqsuccmqr

                _   =nt Nt.add (Nt.mul m q) (Nt.succ r)
                        := Nt.eq_symm (Nt.add_succ_right (Nt.mul m q) r)

                _   =nt Nt.add (Nt.mul m q) q
                        := Nt.add_congr_right (Nt.eq_symm hqeqsuccr)

                _   =nt Nt.mul (Nt.succ m) q
                        := Nt.eq_symm (Nt.mul_succ_left m q)

                _   =nt Nt.add (Nt.mul (Nt.succ m) q) Nt.zero
                        := Nt.eq_symm (
                            Nt.add_zero_right (Nt.mul (Nt.succ m) q))

          · constructor

            · exists q
              apply Nt.eq_symm (Nt.add_zero_left q)

            · exact hqpos

        · have hqgesuccr := (Nt.gt_iff_ge_succ q r).mp hqgtr

          exists m, (Nt.succ r)

          constructor
          · calc
                (Nt.succ a)
                    =nt (Nt.succ (Nt.add (Nt.mul m q) r))
                        := Nt.succ_congr haeqmqr

                _   =nt (Nt.add (Nt.mul m q) (Nt.succ r))
                        := Nt.eq_symm (
                            Nt.add_succ_right (Nt.mul m q) r)

          · constructor
            · exact hqgesuccr
            · exact hqeqsuccr


    apply Nt.induction P h_base h_step n


/- Exponentiation definition -/


axiom Nt.pow : Nt → Nt → Nt

axiom Nt.pow_zero (a : Nt) :
    Nt.pow a Nt.zero =nt Nt.one

axiom Nt.pow_succ (a b : Nt) :
    Nt.pow a (Nt.succ b) =nt Nt.mul a (Nt.pow a b)


/- Exponentiation properties -/



theorem Nt.pow_one (a : Nt) : Nt.pow a Nt.one =nt a := by
    unfold Nt.one

    calc
        Nt.pow a (Nt.succ Nt.zero)
            =nt Nt.mul a (Nt.pow a Nt.zero)
                := Nt.pow_succ a Nt.zero

        _   =nt Nt.mul a Nt.one
                := Nt.mul_congr_right (Nt.pow_zero a)

        _   =nt a
                := Nt.mul_one_right a


theorem Nt.pow_two (a : Nt) : Nt.pow a Nt.two =nt Nt.mul a a := by
    unfold Nt.two

    calc
        Nt.pow a (Nt.succ Nt.one)
            =nt Nt.mul a (Nt.pow a Nt.one)
                := Nt.pow_succ a Nt.one

        _   =nt Nt.mul a a
                := Nt.mul_congr_right (Nt.pow_one a)


theorem Nt.quadratic_identity (a b : Nt) :
    Nt.pow (Nt.add a b) Nt.two =nt

    Nt.add (Nt.pow a Nt.two)
        (Nt.add
            (Nt.mul Nt.two (Nt.mul a b))
            (Nt.pow b Nt.two))

    := by

    calc
        (Nt.pow (Nt.add a b) Nt.two)
            =nt (Nt.mul (Nt.add a b) (Nt.add a b))
                := Nt.pow_two (Nt.add a b)

        _   =nt (Nt.add (Nt.mul (Nt.add a b) a) (Nt.mul (Nt.add a b) b))
                := Nt.mul_distr_right (Nt.add a b) a b

        _   =nt (Nt.add
                    (Nt.add (Nt.mul a a) (Nt.mul b a))
                    (Nt.mul (Nt.add a b) b))
                := Nt.add_congr_left (Nt.mul_distr_left a a b)

        _   =nt (Nt.add
                    (Nt.add (Nt.mul a a) (Nt.mul b a))
                    (Nt.add (Nt.mul a b) (Nt.mul b b)))
                := Nt.add_congr_right (Nt.mul_distr_left b a b)

        _   =nt (Nt.add
                    (Nt.add (Nt.mul a a) (Nt.mul a b))
                    (Nt.add (Nt.mul a b) (Nt.mul b b)))
                := Nt.add_congr_left (Nt.add_congr_right (
                    Nt.mul_comm b a))

        _   =nt (Nt.add
                    (Nt.add
                        (Nt.add (Nt.mul a a) (Nt.mul a b))
                        (Nt.mul a b))
                    (Nt.mul b b))
                := Nt.add_ass (Nt.add (Nt.mul a a) (Nt.mul a b))
                    (Nt.mul a b) (Nt.mul b b)

        _   =nt (Nt.add
                    (Nt.add
                        (Nt.mul a a)
                        (Nt.add (Nt.mul a b) (Nt.mul a b)))
                    (Nt.mul b b))
                := Nt.add_congr_left (Nt.eq_symm (
                    Nt.add_ass (Nt.mul a a) (Nt.mul a b) (Nt.mul a b)))

        _   =nt (Nt.add
                    (Nt.add
                        (Nt.mul a a)
                        (Nt.mul Nt.two (Nt.mul a b)))
                    (Nt.mul b b))
                := Nt.add_congr_left (Nt.add_congr_right (
                    Nt.eq_symm (Nt.mul_two_left (Nt.mul a b))))

        _   =nt (Nt.add
                    (Nt.mul a a)
                    (Nt.add
                        (Nt.mul Nt.two (Nt.mul a b))
                        (Nt.mul b b)))
                := Nt.eq_symm (Nt.add_ass (Nt.mul a a)
                    (Nt.mul Nt.two (Nt.mul a b)) (Nt.mul b b))

        _   =nt (Nt.add
                    (Nt.pow a Nt.two)
                    (Nt.add
                        (Nt.mul Nt.two (Nt.mul a b))
                        (Nt.mul b b)))
                := Nt.add_congr_left (Nt.eq_symm (Nt.pow_two a))

        _   =nt (Nt.add
                    (Nt.pow a Nt.two)
                    (Nt.add
                        (Nt.mul Nt.two (Nt.mul a b))
                        (Nt.pow b Nt.two)))
                := Nt.add_congr_right (Nt.add_congr_right (
                    Nt.eq_symm (Nt.pow_two b)))


