import St.Addition


-- Order definition


def Nt.ge (a b : Nt) : Prop := ∃ c : Nt, a =nt Nt.add b c


-- Order properties


theorem Nt.ge_rfl (a : Nt) : Nt.ge a a := by
    exists Nt.zero
    calc
        a =nt Nt.add a Nt.zero :=
            Nt.eq_symm (Nt.add_zero_right a)


theorem Nt.ge_trans {a b c : Nt}
    (hgeab : Nt.ge a b) (hgebc : Nt.ge b c) : Nt.ge a c := by

    rcases hgeab with ⟨d, habd⟩
    rcases hgebc with ⟨e, hbce⟩

    exists Nt.add e d

    calc
        a =nt (Nt.add b d)
            := habd

        _ =nt (Nt.add (Nt.add c e) d)
            := Nt.add_congr_left hbce

        _ =nt (Nt.add c (Nt.add e d))
            := Nt.eq_symm (Nt.add_ass c e d)

theorem Nt.ge_antisym {a b : Nt}
    (hgeab : ge a b) (hgeba : ge b a) : a =nt b := by

    rcases hgeab with ⟨c, habc⟩
    rcases hgeba with ⟨e, hbae⟩

    have hbbce : b =nt Nt.add b (Nt.add c e) := by

        calc
            b =nt Nt.add a e := hbae
            _ =nt Nt.add (Nt.add b c) e := Nt.add_congr_left habc
            _ =nt Nt.add b (Nt.add c e) := Nt.eq_symm (Nt.add_ass b c e)

    let P (n : Nt) : Prop :=

        (n =nt Nt.add n (Nt.add c e)) → (Nt.add n c) =nt n

    have h_base : P Nt.zero := by
        intro h

        have hzeroce : Nt.zero =nt Nt.add c e := by

            calc
                Nt.zero
                    =nt Nt.add Nt.zero (Nt.add c e) := h
                _   =nt Nt.add c e := Nt.add_zero_left (Nt.add c e)

        replace hzeroce :=
            Nt.add_equal_zero_then_zero (Nt.eq_symm hzeroce)

        rcases hzeroce with ⟨hzeroc, hzeroe⟩

        calc
            (Nt.add Nt.zero c)
                =nt (Nt.add Nt.zero Nt.zero)
                := Nt.add_congr_right hzeroc

            _   =nt Nt.zero := Nt.add_zero_left Nt.zero


    have h_step : ∀ (n : Nt), P n → P (Nt.succ n) := by

        intro n hPn hsuccnnce

        have hnnce :
            (Nt.succ n) =nt Nt.succ (Nt.add n (Nt.add c e))
                := by
            calc
                (Nt.succ n)
                    =nt Nt.add (Nt.succ n) (Nt.add c e)
                        := hsuccnnce
                _   =nt Nt.succ (Nt.add n (Nt.add c e))
                        := Nt.add_succ_left n (Nt.add c e)

        replace hnnce := Nt.succ_inj hnnce

        have h : (Nt.succ (Nt.add n c) =nt (Nt.succ n)) := by

            apply Nt.succ_congr (hPn hnnce)


        calc
            (Nt.add (Nt.succ n) c)
                =nt (Nt.succ (Nt.add n c))
                    := Nt.add_succ_left n c

            _   =nt (Nt.succ n)
                    := h

    have h : P b := Nt.induction P h_base h_step b

    calc
        a =nt Nt.add b c := habc
        _ =nt b := h hbbce


theorem Nt.ge_add (a b c : Nt) :
    (Nt.ge a b) ↔ (Nt.ge (Nt.add a c) (Nt.add b c)) := by

    constructor
    · intro h
      rcases h with ⟨d, habd⟩
      exists d

      calc
        (Nt.add a c)
            =nt (Nt.add (Nt.add b d) c)
                := Nt.add_congr_left habd

        _   =nt (Nt.add b (Nt.add d c))
            := Nt.eq_symm (Nt.add_ass b d c)

        _   =nt (Nt.add b (Nt.add c d))
            := Nt.add_congr_right (Nt.add_comm d c)

        _   =nt (Nt.add (Nt.add b c) d)
            := Nt.add_ass  b c d

    · intro h
      rcases h with ⟨d, hacbcd⟩

      exists d

      let P (n : Nt) : Prop :=

        ((Nt.add a n) =nt (Nt.add (Nt.add b n) d)) →
        (a =nt (Nt.add b d))

      have h_base : P Nt.zero := by
        intro hanbnd

        calc
            a =nt Nt.add a Nt.zero
                := Nt.eq_symm (Nt.add_zero_right a)

            _ =nt Nt.add (Nt.add b Nt.zero) d
                := hanbnd

            _ =nt Nt.add b d
                := Nt.add_congr_left (Nt.add_zero_right b)

      have h_step : ∀ (n : Nt), P n → P (Nt.succ n) := by

        intro n hPn hsuccanbnd
        have hanbnd :
            Nt.succ (Nt.add a n) =nt
            Nt.succ (Nt.add (Nt.add b n) d) := by

            calc
                Nt.succ (Nt.add a n)
                    =nt Nt.add a (Nt.succ n)
                        := Nt.eq_symm (Nt.add_succ_right a n)
                _   =nt Nt.add (Nt.add b (Nt.succ n)) d
                        := hsuccanbnd
                _   =nt Nt.add (Nt.succ (Nt.add b n)) d
                        := Nt.add_congr_left (Nt.add_succ_right b n)
                _   =nt Nt.succ (Nt.add (Nt.add b n) d)
                        := Nt.add_succ_left (Nt.add b n) d

        replace hanbnd := Nt.succ_inj hanbnd

        apply hPn hanbnd

      have h : P c := Nt.induction P h_base h_step c

      apply h hacbcd


def Nt.gt (a b : Nt) : Prop := Nt.ge a b ∧ ((a =nt b) → False)


theorem Nt.gt_iff_ge_succ (a b : Nt) :
    Nt.gt a b ↔ Nt.ge a (Nt.succ b) := by

    constructor

    · intro h

      rcases h with ⟨hge, haneb⟩
      rcases hge with ⟨c, haeqbc⟩

      have hbcneb : (Nt.add b c =nt b) → False := by

          intro hbceqb
          apply haneb

          calc
              a =nt (Nt.add b c) := haeqbc
              _ =nt b := hbceqb

      have hcnezero : (c =nt Nt.zero) → False := by

        intro hceqzero
        apply hbcneb
        calc
            (Nt.add b c)
                =nt (Nt.add b Nt.zero)
                    := Nt.add_congr_right hceqzero

            _   =nt b
                    := Nt.add_zero_right b

      have ⟨d, hsuccdeqc, hdunique⟩ := Nt.unique_ante hcnezero

      exists d

      calc
          a =nt (Nt.add b c)
            := haeqbc

          _ =nt (Nt.add b (Nt.succ d))
            := Nt.add_congr_right (Nt.eq_symm hsuccdeqc)

          _ =nt Nt.succ (Nt.add b d)
            := (Nt.add_succ_right b d)

          _ =nt Nt.add (Nt.succ b) d
            := Nt.eq_symm (Nt.add_succ_left b d)


    · intro h

      rcases h with ⟨d, haeqsuccbd⟩

      constructor
      · exists (Nt.succ d)
        calc
            a =nt (Nt.add (Nt.succ b) d)
                    := haeqsuccbd

            _   =nt Nt.succ (Nt.add b d)
                    := Nt.add_succ_left b d

            _   =nt Nt.add b (Nt.succ d)
                    := Nt.eq_symm (Nt.add_succ_right b d)

      · intro haneb

        apply Nt.succ_ne_zero d

        apply Nt.add_canc_left b

        calc
            (Nt.add b (Nt.succ d))
                =nt (Nt.succ (Nt.add b d))
                    := Nt.add_succ_right b d

            _   =nt (Nt.add (Nt.succ b) d)
                    := Nt.eq_symm (Nt.add_succ_left b d)

            _   =nt a
                    := Nt.eq_symm haeqsuccbd

            _   =nt b
                    := haneb

            _   =nt (Nt.add b Nt.zero)
                    := Nt.eq_symm (Nt.add_zero_right b)


theorem Nt.gt_exists_pos (a b : Nt):
   Nt.gt a b ↔ (∃ c : Nt, Nt.pos c ∧ (a =nt (Nt.add b c))) := by

   constructor
   · intro hagtb

     rcases hagtb with ⟨hageb, haneb⟩
     rcases hageb with ⟨d, haeqbd⟩

     exists d

     constructor
     · intro hdnezero
       apply haneb

       calc
        a =nt (Nt.add b d)
            := haeqbd

        _ =nt (Nt.add b Nt.zero)
            := Nt.add_congr_right hdnezero

        _ =nt b
            := Nt.add_zero_right b


     · exact haeqbd

   · intro h

     rcases h with ⟨d, h⟩
     rcases h with ⟨hdpos, haeqbd⟩

     constructor
     · exists d

     · intro haeqb
       apply hdpos
       apply Nt.add_canc_left b

       calc
        (Nt.add b d)
            =nt a
                := Nt.eq_symm haeqbd

        _   =nt b
                := haeqb

        _   =nt (Nt.add b Nt.zero)
                := Nt.eq_symm (Nt.add_zero_right b)


theorem Nt.order_trichotomy (a b : Nt) :
    (a =nt b) ∨ (Nt.gt a b) ∨ (Nt.gt b a) := by

    let P (n m : Nt) : Prop :=
        (n =nt m) ∨ (Nt.gt n m) ∨ (Nt.gt m n)

    have h_base : ∀ (m : Nt), P Nt.zero m := by

        let P_base (m : Nt) : Prop := P Nt.zero m

        have h_base_base : P Nt.zero Nt.zero := by

            left
            exact Nt.eq_rfl

        have h_base_step :
            ∀ (m : Nt), P Nt.zero m → P Nt.zero (Nt.succ m) := by

            intro m hPm
            right
            right
            constructor
            · exists (Nt.succ m)
              exact Nt.eq_symm (Nt.add_zero_left (Nt.succ m))
            · apply Nt.succ_ne_zero

        intro m
        apply (Nt.induction P_base h_base_base h_base_step m)

    have h_step : ∀ (m : Nt), ∀ (n : Nt), P n m → P (Nt.succ n) m := by

        let P_step (m : Nt) : Prop :=
            ∀ (n : Nt), P n m → P (Nt.succ n) m

        have h_step_base :
            ∀ (n : Nt), P n Nt.zero → P (Nt.succ n) Nt.zero := by

            intro n hPn

            right
            left
            constructor
            · exists (Nt.succ n)
              exact Nt.eq_symm (Nt.add_zero_left (Nt.succ n))

            · apply Nt.succ_ne_zero

        have h_step_step :
            ∀ (m : Nt),
                (∀ (n : Nt),
                    P n m → P (Nt.succ n) m)
                →
                (∀ (n : Nt),
                    P n (Nt.succ m) → P (Nt.succ n) (Nt.succ m))
                := by

            intro m hPm n hPn

            rcases hPn with h_neqsuccm | h_ngtsuccm | h_succmgtn
            · right
              left
              constructor
              · exists (Nt.succ Nt.zero)
                -- succ a = add (succ m) (succ zero)

                calc
                    (Nt.succ n)
                        =nt Nt.add (Nt.succ n) Nt.zero
                            := Nt.eq_symm
                                (Nt.add_zero_right (Nt.succ n))

                    _   =nt (Nt.succ (Nt.add n Nt.zero))
                            := Nt.add_succ_left n Nt.zero

                    _   =nt (Nt.add n (Nt.succ Nt.zero))
                            := Nt.eq_symm (Nt.add_succ_right n Nt.zero)

                    _   =nt (Nt.add (Nt.succ m) (Nt.succ Nt.zero))
                            := Nt.add_congr_left h_neqsuccm

              · intro hsuccneqsuccm -- h : succ n = succ m -> False

                apply (Nt.succ_ne_zero Nt.zero)
                apply Nt.add_canc_left m

                have hneqm : n =nt m := Nt.succ_inj hsuccneqsuccm

                calc -- add m (succ zero) = add m zero
                    Nt.add m (Nt.succ Nt.zero)
                        =nt Nt.succ (Nt.add m Nt.zero)
                            := Nt.add_succ_right m Nt.zero

                    _   =nt Nt.add (Nt.succ m) Nt.zero
                            := Nt.eq_symm (Nt.add_succ_left m Nt.zero)

                    _   =nt Nt.add n Nt.zero
                            := Nt.eq_symm
                                (Nt.add_congr_left h_neqsuccm)

                    _   =nt Nt.add m Nt.zero
                            := Nt.add_congr_left hneqm

            · rcases h_ngtsuccm with ⟨hngesuccm, hnnesuccm⟩
              rcases hngesuccm with ⟨c, hneqsuccmc⟩

              right
              left

              constructor
              · exists (Nt.succ c)

                calc
                    (Nt.succ n)
                        =nt (Nt.succ (Nt.add (Nt.succ m) c))
                            := (Nt.succ_congr hneqsuccmc)

                    _   =nt (Nt.add (Nt.succ m) (Nt.succ c))
                            := (Nt.eq_symm
                                (Nt.add_succ_right (Nt.succ m) c))

              · intro hsuccneqsuccm

                apply Nt.succ_ne_zero c

                apply Nt.add_canc_left m


                have hneqm : n =nt m := Nt.succ_inj hsuccneqsuccm

                calc
                    (Nt.add m (Nt.succ c))
                        =nt (Nt.succ (Nt.add m c))
                            := Nt.add_succ_right m c

                    _   =nt (Nt.add (Nt.succ m) c)
                            := Nt.eq_symm (Nt.add_succ_left m c)

                    _   =nt n
                            := Nt.eq_symm hneqsuccmc

                    _   =nt m
                            := hneqm

                    _   =nt (Nt.add m Nt.zero)
                            := Nt.eq_symm (Nt.add_zero_right m)

            · rcases h_succmgtn with ⟨hsuccmgen, hsuccmnen⟩
              rcases hsuccmgen with ⟨c, hsuccmeqnc⟩

              by_cases h : (m =nt n)
              · left
                apply Nt.succ_congr
                replace h := Nt.eq_symm h
                exact h

              · right
                right

                constructor
                · have hcnezero : (c =nt Nt.zero) → False := by

                    intro hceqzero
                    apply hsuccmnen

                    calc
                        (Nt.succ m)
                            =nt (Nt.add n c)
                                := hsuccmeqnc

                        _   =nt (Nt.add n Nt.zero)
                                := (Nt.add_congr_right hceqzero)

                        _   =nt n
                                := Nt.add_zero_right n

                  have ⟨d, hsuccdeqc, huniqued⟩
                        := Nt.unique_ante hcnezero

                  exists d

                  calc
                    (Nt.succ m)
                        =nt (Nt.add n c)
                            := hsuccmeqnc

                    _   =nt (Nt.add n (Nt.succ d))
                            := Nt.eq_symm (Nt.add_congr_right hsuccdeqc)

                    _   =nt (Nt.succ (Nt.add n d))
                            := (Nt.add_succ_right n d)

                    _   =nt (Nt.add (Nt.succ n) d)
                            := Nt.eq_symm (Nt.add_succ_left n d)

                · intro hsuccmeqsuccn
                  apply h
                  have hmeqn := Nt.succ_inj hsuccmeqsuccn
                  exact hmeqn


        intro m
        apply (Nt.induction P_step h_step_base h_step_step m)

    let P_b (a : Nt) : Prop := P a b

    apply Nt.induction P_b (h_base b) (h_step b) a


theorem Nt.zero_gt_false (a : Nt) : Nt.gt Nt.zero a → False := by

    let P (n : Nt) : Prop := Nt.gt Nt.zero n → False

    have h_base : P Nt.zero := by

        intro hzerogtzero

        rcases hzerogtzero with ⟨hzerogezero, hzeronezero⟩

        apply hzeronezero

        apply Nt.eq_rfl

    have h_step : ∀ (n : Nt), P n → P (Nt.succ n) := by

        intro n hzerogtnfalse hzerogtsuccn

        rcases hzerogtsuccn with ⟨hzerogesuccn, hzeronesuccn⟩

        rcases hzerogesuccn with ⟨c, hzeroeqsuccnc⟩

        apply hzerogtnfalse

        constructor
        · exists (Nt.succ c)

          calc
            Nt.zero
                =nt Nt.add (Nt.succ n) c
                    := hzeroeqsuccnc

            _   =nt Nt.succ (Nt.add n c)
                    := Nt.add_succ_left n c

            _   =nt Nt.add n (Nt.succ c)
                    := Nt.eq_symm (Nt.add_succ_right n c)


        · intro hzeronen

          apply Nt.succ_ne_zero (Nt.add n c)

          apply Nt.eq_symm

          calc
            Nt.zero
                =nt Nt.add (Nt.succ n) c
                    := hzeroeqsuccnc

            _   =nt Nt.succ (Nt.add n c)
                    := Nt.add_succ_left n c

    apply Nt.induction P h_base h_step a


theorem Nt.ge_zero_eq_zero (a : Nt) :
    Nt.ge Nt.zero a → (Nt.zero =nt a) := by

    intro hzerogea

    by_cases hzeroeqa: (Nt.zero =nt a)
    · exact hzeroeqa
    · have hzerogta : Nt.gt Nt.zero a := ⟨hzerogea, hzeroeqa⟩

      exfalso
      apply Nt.zero_gt_false a

      exact hzerogta

theorem Nt.gt_succ_then_ge (a b : Nt) :
    Nt.gt (Nt.succ a) b → Nt.ge a b := by

    let P (m : Nt) : Prop :=
        ∀ (n : Nt), Nt.gt (Nt.succ n) m → Nt.ge n m

    have h_base : P Nt.zero := by

        intro n hsuccngtm

        exists n

        apply Nt.eq_symm

        exact Nt.add_zero_left n

    have h_step : ∀ (m : Nt), P m → P (Nt.succ m) := by

        intro m hPm n hsuccngtsuccm

        rcases hsuccngtsuccm with ⟨hsuccngesuccm, hsuccnnesuccm⟩
        rcases hsuccngesuccm with ⟨c, hsuccneqsuccmc⟩

        have hcnezero : (c =nt Nt.zero) → False := by

            intro hceqzero
            apply hsuccnnesuccm
            calc
                (Nt.succ n)
                    =nt Nt.add (Nt.succ m) c
                        := hsuccneqsuccmc

                _   =nt Nt.add (Nt.succ m) Nt.zero
                        := Nt.add_congr_right hceqzero

                _   =nt Nt.succ m
                        := Nt.add_zero_right (Nt.succ m)


        have ⟨d, hsuccdeqc, huniqued⟩ := unique_ante hcnezero

        exists d

        have hneqmc : (n =nt Nt.add m c) := by

            apply Nt.succ_inj

            calc
                (Nt.succ n)
                    =nt Nt.add (Nt.succ m) c
                        := hsuccneqsuccmc

                _   =nt Nt.succ (Nt.add m c)
                        := Nt.add_succ_left m c

        calc
            n =nt Nt.add m c
                    := hneqmc

            _ =nt Nt.add m (Nt.succ d)
                    := Nt.eq_symm (Nt.add_congr_right hsuccdeqc)

            _ =nt Nt.succ (Nt.add m d)
                    := Nt.add_succ_right m d

            _ =nt (Nt.add (Nt.succ m) d)
                    := Nt.eq_symm (Nt.add_succ_left m d)

    have P_b := Nt.induction P h_base h_step b

    exact P_b a



theorem strong_induction {P' : Nt → Prop} {b0 : Nt}

    (hstrong : ∀ a : Nt, Nt.ge a b0 →
    (∀ b : Nt, Nt.ge b b0 → Nt.gt a b → P' b) → P' a) :

    ∀ a : Nt, Nt.ge a b0 → P' a := by


    let P (n : Nt) : Prop := Nt.ge n b0 →
        ∀ m : Nt, Nt.ge m b0 → Nt.ge n m → P' m

    let Pgt (n : Nt) : Prop :=
        ∀ m : Nt, Nt.ge m b0 → Nt.gt n m → P' m


    have h_base : P Nt.zero := by

        intro hzerogeb0 m hmgeb0 hzerogem

        have hPgt : Pgt Nt.zero := by

            intro m _ hzerogtm

            exfalso

            apply Nt.zero_gt_false m

            exact hzerogtm

        replace hstrong := hstrong Nt.zero hzerogeb0

        replace hstrong := hstrong hPgt

        have hzeroeqm := Nt.ge_zero_eq_zero m hzerogem

        apply Nt.prop_congr hzeroeqm

        exact hstrong


    have h_step : ∀ n : Nt, P n → P (Nt.succ n) := by

        intro n hPn hsuccngeb0

        replace hstrong := hstrong (Nt.succ n) hsuccngeb0

        have hPgt : Pgt (Nt.succ n) := by

            intro m hmgeb0 hsuccngtm

            have hngem := Nt.gt_succ_then_ge n m hsuccngtm

            have hngeb0 := Nt.ge_trans hngem hmgeb0

            apply hPn hngeb0 m hmgeb0 hngem

        have hP'succn := hstrong hPgt

        intro m hmgeb0 hsuccngem

        by_cases hsuccneqm : (Nt.succ n =nt m)

        · apply Nt.prop_congr hsuccneqm

          exact hP'succn

        · have hsuccngtm : Nt.gt (Nt.succ n) m := ⟨hsuccngem, hsuccneqm⟩

          have hngem := Nt.gt_succ_then_ge n m hsuccngtm

          have hngeb0 := Nt.ge_trans hngem hmgeb0

          apply hPn hngeb0 m hmgeb0 hngem


    intro a hageb0

    have P_a := Nt.induction P h_base h_step a

    apply P_a hageb0 a hageb0 (Nt.ge_rfl a)


theorem backward_induction {P' : Nt → Prop} {a : Nt}

    (h_stepward : (∀ b : Nt, P' (Nt.succ b) → P' b))
    (h_baseward : P' a) :

    ∀ b : Nt, Nt.ge a b → P' b := by


    let P (n : Nt) : Prop :=
        (∀ m : Nt, P' (Nt.succ m) → P' m) → P' n →

        ∀ m : Nt, Nt.ge n m → P' m

    have h_base : P Nt.zero := by

        intro h_stepwardzero h_basewardzero m hzerogem

        have hzeroeqm := Nt.ge_zero_eq_zero m hzerogem

        apply Nt.prop_congr (a:=Nt.zero) (b:=m) hzeroeqm

        exact h_basewardzero


    have h_step : ∀ n : Nt, P n → P (Nt.succ n) := by

        intro n hPn h_stepwardsuccn h_basewardsuccn m hsuccngem

        by_cases hsuccneqm : (Nt.succ n =nt m)

        · apply Nt.prop_congr (a:=(Nt.succ n)) (b:=m) hsuccneqm

          exact h_basewardsuccn

        · have h_basewardn := h_stepwardsuccn n h_basewardsuccn

          have hsuccngtm : Nt.gt (Nt.succ n) m := ⟨hsuccngem, hsuccneqm⟩

          have hngem := Nt.gt_succ_then_ge n m hsuccngtm

          apply hPn h_stepwardsuccn h_basewardn m hngem

    have P_a := Nt.induction P h_base h_step a

    intro b hageb

    exact P_a h_stepward h_baseward b hageb



