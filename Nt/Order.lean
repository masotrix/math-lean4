import Nt.Addition


-- Order definition


def ge (a b : Nt) : Prop := ∃ c : Nt, a = add b c


-- Order properties


theorem ge_refl (a : Nt) : ge a a := by
  -- Existe cero
  -- ∃ c : Nt, a = add a c
  -- =>
  -- a = add a zero
  exists Nt.zero

theorem ge_trans {a b c : Nt}
  (hab : ge a b) (hbc : ge b c) : ge a c := by

  -- Obtener "d" y reemplazar "a" por (add b d)
  -- ge a c
  -- =>
  -- ge (add b d) c
  obtain ⟨d, rfl⟩ := hab

  -- Obtener "e" y reemplazar "b" por (add c e)
  -- ge (add b d) c
  -- =>
  -- ge (add (add c e) d) c
  obtain ⟨e, rfl⟩ := hbc

  -- Adicion asociativa
  -- ge (add (add c e) d) c
  -- =>
  -- ge (add c (add e d)) c
  rw [← add_ass]

  -- Existe (add e d)
  -- ge (add c (add e d)) c
  -- =>
  -- add c (add e d) = add c (add e d)
  exists (add e d)

theorem ge_antisym {a b : Nt}
  (hab : ge a b) (hba : ge b a) : a = b := by

  -- Obtener "c" y reemplazar "a" por (add b c)
  -- a = b
  -- =>
  -- add b c = b
  -- (hba : ge b a)
  -- =>
  -- (hba : ge b (add b c)
  obtain ⟨c, rfl⟩ := hab

  -- Obtener "e" y crear h
  -- (h : none)
  -- =>
  -- (h : b = add (add b c) e
  obtain ⟨e, h⟩ := hba

  -- Adicion asociativa sobre h
  -- (h : b = add (add b c) e
  -- =>
  -- (h : b = add b (add c e)
  rw [← add_ass] at h

  induction b with

  | zero =>

    -- Adicion de cero por la izquierda
    -- (h : zero = add zero (add c e)
    -- =>
    -- (h : zero = add c e)
    rw [add_zero_left] at h

    -- Adicion suma cero => sumandos cero
    -- (h : zero = add c e)
    -- =>
    -- (h : (c = zero) ∧ (e = zero))
    replace h := add_equal_zero_then_zero (Eq.symm h)

    -- Separar conjuncion en h
    -- (hc : none, he : none)
    -- =>
    -- (hc : c = zero, he : e = zero)
    obtain ⟨hc, he⟩ := h

    -- Usar (c = zero) en objetivo
    -- add b c = b
    -- =>
    -- add b zero = b
    rw [hc]

    -- Adicion de zero por la derecha
    -- add b zero = b
    -- =>
    -- b = b
    rw [add_zero_right]

  | succ b ih =>

    -- Adicion de sucesor por la izquierda
    -- add (succ b) c = succ b
    -- =>
    -- succ (add b c) = succ b
    rw [add_succ_left]

    -- Sucesor como funcion
    -- succ (add b c) = succ b
    -- =>
    -- add b c = b
    apply succ_func

    -- Hipotesis inductiva
    -- add b c = b
    -- =>
    -- b = add b (add c e)
    apply ih

    -- Adicion de sucesor por la izquierda sobre h
    -- (h: succ b = add (succ b) (add c e))
    -- =>
    -- (h: succ b = succ (add b (add c e)))
    rw [add_succ_left] at h

    -- Sucesor injectiva sobre h
    -- (h: succ b = succ (add b (add c e)))
    -- =>
    -- (h: b = add b (add c e))
    replace h := succ_inj h

    exact h

theorem ge_add (a b c : Nt) :
    (ge a b) ↔ (ge (add a c) (add b c)) := by

    constructor

    · -- Mover hipotesis de implicancia a hipotesis de teorema
      -- (ge a b) -> (ge (add a c) (add b c))
      -- =>
      -- (ge (add a c) (add b c))
      -- (h : none)
      -- =>
      -- (h : ge a b)
      intro h

      -- Obtener "d" y reemplazar "a" por (add b d)
      -- ge (add a c) (add b c)
      -- =>
      -- ge (add (add b d) c) (add b c)
      -- (h : ge a b)
      -- =>
      -- (h : a = add b d)
      obtain ⟨d, rfl⟩ := h

      -- Adicion asociativa
      -- ge (add (add b d) c) (add b c)
      -- =>
      -- ge (add b (add d c)) (add b c)
      rw [← add_ass]

      -- Existe "d"
      -- ge (add b (add d c)) (add b c)
      -- =>
      -- add b (add d c) = add (add b c) d
      exists d

      -- Adicion asociativa
      -- add b (add d c) = add (add b c) d
      -- =>
      -- add b (add d c) = add b (add c d)
      rw [← add_ass]

      -- Adicion conmutativa
      -- add b (add d c) = add b (add c d)
      -- =>
      -- add b (add c d) = add b (add c d)
      conv =>
        lhs
        arg 2
        rw [add_comm]

    · -- Mover hipotesis de implicancia a hipotesis de teorema
      -- (ge (add a c) (add b c)) -> (ge a b)
      -- =>
      -- (ge a b)
      -- (h : none)
      -- =>
      -- (h : ge (add a c) (add b c))
      intro h

      -- Obtener "d" y reemplazar (add a c) por (add (add b c) d)
      -- (h : ge (add a c) (add b c))
      -- =>
      -- (h : add a c = add (add b c) d
      obtain ⟨d, h⟩ := h

      -- Existe "d"
      -- (ge a b)
      -- =>
      -- a = add b d
      exists d

      induction c with

      | zero =>

        -- Adicion de cero por la derecha en h
        -- (h : add a zero = add (add b zero) d
        -- =>
        -- (h : a = add (add b zero) d
        rw [add_zero_right] at h

        -- Adicion de cero por la derecha en h
        -- (h : a = add (add b zero) d
        -- =>
        -- (h : a = add b d
        rw [add_zero_right] at h
        exact h

      | succ c ih =>

        -- Adicion de sucesor por la derecha
        -- (h : add a (succ c) = add (add b (succ c) d))
        -- =>
        -- (h : succ (add a c) = add (add b (succ c) d))
        rw [add_succ_right] at h

        -- Adicion de sucesor por la derecha
        -- (h : succ (add a c) = add (add b (succ c)) d)
        -- =>
        -- (h : succ (add a c) = add (succ (add b c) d))
        rw [add_succ_right] at h

        -- Adicion de sucesor por la izquierda
        -- (h : succ (add a c) = add (succ (add b c)) d)
        -- =>
        -- (h : succ (add a c) = succ (add (add b c) d))
        rw [add_succ_left] at h

        -- Inyectividad de sucesor
        -- (h : succ (add a c) = succ (add (add b c) d))
        -- =>
        -- (h : add a c = add (add b c) d)
        replace h := succ_inj h

        apply ih

        exact h

def gt (a b : Nt) : Prop := ge a b ∧ a ≠ b

theorem gt_succ_ge (a b : Nt) :
    gt a b ↔ ge a (Nt.succ b) := by

    constructor

    · intro h

      -- Obtener "hge" y "hne" desde conjuncion h
      -- (hge : none)
      -- =>
      -- (hge : ge a b)
      -- (hne : none)
      -- =>
      -- (hne : a ≠ b)
      obtain ⟨hge, hne⟩ := h

      -- Obtener "c" y reemplazar "a" por (add b c)
      -- (hne : a ≠ b)
      -- =>
      -- (hne : (add b c) ≠ b)
      -- ge a (succ b)
      -- =>
      -- ge (add b c) (succ b)
      obtain ⟨c, rfl⟩ := hge

      -- Adicion de zero por la derecha
      -- (hne : add b c ≠ b)
      -- =>
      -- (hne : add b c ≠ add b zero)
      rw [← add_zero_right b] at hne

      -- Cancelar adicion de constante por la izquierda
      -- (hne : add b c ≠ add b zero
      -- =>
      -- (hne : c ≠ zero)
      replace hne := ne_add_canc_left hne

      -- Obtener "d" antecesor de "c"
      -- (hdc : none)
      -- =>
      -- (hdc : succ d = c)
      -- (hdu : none)
      -- =>
      -- (hdu : ∀ d' : Nt, succ d' = c → d' = d)
      have ⟨d, hdc, hdu⟩ := unique_ante hne

      -- Existe "d" que cumple "ge"
      -- ge (add b c) (succ b)
      -- =>
      -- add b c = add (succ b) d
      exists d

      -- Adicion de sucesor por la izquierda
      -- add b c = add (succ b) d
      -- =>
      -- add b c = succ (add b d)
      rw [add_succ_left]

      -- Adicion de sucesor por la izquierda
      -- add b c = succ (add b d)
      -- =>
      -- add b c = add b (succ d)
      rw [← add_succ_right]

      rw [hdc]

    · intro h

      -- Obtener "c" que cumple "ge" en h
      -- (h: ge a (succ b))
      -- =>
      -- (h: a = add (succ b) c
      -- gt a b
      -- =>
      -- gt (add (succ b) c) b
      obtain ⟨c, rfl⟩ := h

      -- Adicion de sucesor por la izquierda
      -- gt (add (succ b) c) b
      -- =>
      -- gt (succ (add  b c)) b
      rw [add_succ_left]

      -- Adicion de sucesor por la derecha
      -- gt (succ (add b c)) b
      -- =>
      -- gt (add b (succ c)) b
      rw [← add_succ_right]

      constructor

      · -- Existe "succ c" que cumple "ge"
        -- ge (add b (succ c)) b
        -- =>
        -- add b (succ c) = add b (succ c)
        exists (Nt.succ c)

      · -- Mover hipotesis de induccion a hipotesis de teorema
        -- add b (succ c) ≠ b
        -- =>
        -- False
        -- (hne: none)
        -- =>
        -- (hne: add b (succ c) = b)
        intro hne

        -- Adicion de zero por la derecha
        -- (hne: add b (succ c) = b)
        -- =>
        -- (hne: add b (succ c) = add b zero)
        rw [← add_zero_right b] at hne

        -- Cancelar suma de constante por la izquierda
        -- (hne: add b (succ c) = add b zero)
        -- =>
        -- (hne: succ c = zero)
        replace hne := add_canc_left hne

        -- Sucesor distinto de zero
        -- False
        -- =>
        -- succ c = zero
        apply succ_ne_zero c

        exact hne

theorem gt_exists_pos (a b : Nt) :
    gt a b ↔ (∃ c : Nt, Pos c ∧ a = add b c) := by

    constructor

    · -- Mover hipotesis de induccion a hipotesis de teorema
      -- (h : none)
      -- =>
      -- (h : gt a b)
      -- gt a b → (∃ c : Nt, Pos c ∧ a = add b c)
      -- =>
      -- ∃ c : Nt, Pos c ∧ a = add b c
      intro h

      -- Separar hipotesis conjungadas en h
      -- (hge: none)
      -- =>
      -- (hge: ge a b)
      -- (hne: none)
      -- =>
      -- (hne: a ≠ b)
      obtain ⟨hge, hne⟩ := h

      -- Obtener "d" desde "hge"
      -- (hne : a ≠ b)
      -- =>
      -- (hne : add b d ≠ b)
      -- (∧2 : a = add b c)
      -- =>
      -- (∧2 : add b d = add b c)
      obtain ⟨d, rfl⟩ := hge

      -- Exists "d"
      -- ∃ c : Nt, Pos c ∧ b d = add b c
      -- =>
      -- Pos d ∧ b d = add b d
      exists d

      constructor

      · -- Mover hipotesis de induccion a hipotesis de teorema
        -- (h : none)
        -- =>
        -- (h : d = zero)
        -- d = zero → False
        -- =>
        -- False
        intro h

        -- Aplicar hne "add b d = b → False"
        -- False
        -- =>
        -- add b d = b
        apply hne

        -- Adicion de zero por la derecha
        -- add b d = b
        -- =>
        -- add b d = add b zero
        rw [← add_zero_right b]

        -- Adicion de constante por la izquierda
        -- add b d = add b zero
        -- =>
        -- d = zero
        apply add_const_left

        -- Calzar hipotesis h "d = zero"
        exact h

      · -- Reflexion
        -- add b d = add b d
        rfl

    · -- Mover hipotesis de implicancia a hipotesis de teorema
      -- (h : none)
      -- =>
      -- (h : ∃ c : Nt, Pos c ∧ a = add b c)
      -- (∃ c : Nt, Pos c ∧ a = add b c) → gt a b
      -- =>
      -- gt a b
      intro h

      -- Obtener "c" que cumple "gt" en h
      -- (h : ∃ c : Nt, Pos c ∧ a = add b c)
      -- =>
      -- (h : Pos c ∧ a = add b c)
      obtain ⟨c, h⟩ := h

      -- Separar hipotesis hpos y heq desde h
      -- (hpos : none)
      -- =>
      -- (hpos : Pos c)
      -- (heq : none)
      -- =>
      -- (heq : a = add b c)
      obtain ⟨hpos, heq⟩ := h

      constructor

      · -- {ge a b}

        -- Existe "c" que cumple "ge"
        -- ge a b
        -- =>
        -- a = add b c
        exists c

        -- Hipotesis (heq : a = add b c)
        -- exact heq

      · -- Hipotesis de implicancia a hipotesis de teorema
        -- (hne : none)
        -- =>
        -- (hne : a = b)
        -- a = b → False
        -- =>
        -- False
        intro hne

        -- Hipotesis (hpos : Pos c)
        -- False
        -- =>
        -- c = zero
        apply hpos

        -- Cancelacion de constante por la izquierda
        -- c = zero
        -- =>
        -- add b c = add b zero
        apply add_canc_left (a := b)

        -- Adicion de cero por la derecha
        -- add b c = add b zero
        -- =>
        -- add b c = b
        rw [add_zero_right]

        -- Hipotesis (heq : a = add b c)
        -- add b c = b
        -- a = b
        rw [← heq]

        -- Hipotesis (hne : a = b)
        exact hne

theorem order_trichotomy (a b : Nt) :
    a = b ∨ gt a b ∨ gt b a := by

    induction a with
    | zero =>

      induction b with
      | zero =>

        -- Izquierda de disyuncion
        -- zero = zero ∨ gt zero zero ∨ gt zero zero
        -- =>
        -- zero = zero
        left
        rfl

      | succ b ih2 =>

        -- Derecha de conjuncion
        -- zero = succ b ∨ gt zero (succ b) ∨ gt (succ b) zero
        -- =>
        -- gt zero (succ b) ∨ gt (succ b) zero
        right

        -- Derecha de conjuncion
        -- gt zero (succ b) ∨ gt (succ b) zero
        -- =>
        -- gt (succ b) zero
        right

        constructor

        · -- Existe "succ b" que cumple "gt"
          -- gt (succ b) zero
          -- =>
          -- succ b = add zero (succ b)
          exists (Nt.succ b)

          -- Adicion de zero por la izquierda
          -- succ b = add zero (succ b)
          -- =>
          -- succ b = succ b
          rw [add_zero_left]

        · -- Sucesor distinto de cero
          -- succ b = zero → False
          -- =>
          -- True
          apply succ_ne_zero

    | succ a ih1 =>

      induction b with
      | zero =>

        -- Derecha de conjuncion
        -- succ a = zero ∨ gt (succ a) zero ∨ gt zero (succ a)
        -- =>
        -- gt (succ a) zero ∨ gt zero (succ a)
        right

        -- Izquierda de conjuncion
        -- gt (succ a) zero ∨ gt zero (succ a)
        -- =>
        -- gt (succ a) zero
        left

        constructor

        · -- Existe "succ a" que cumple "gt"
          -- gt (succ a) zero
          -- =>
          -- succ a = add zero (succ a)
          exists (Nt.succ a)

          -- Adicion de zero por la izquierda
          -- succ a = add zero (succ a)
          -- =>
          -- succ a = succ a
          rw [add_zero_left]

        · -- Sucesor distinto de cero
          -- succ a = zero → False
          -- =>
          -- True
          apply succ_ne_zero

      | succ b ih2 =>

        rcases ih1 with h_eq | h_gt1 | h_gt2

        · /- (h_eq : a = succ b) -/

          -- Derecha de conjuncion
          -- succ a = succ b ∨ gt (succ a) (succ b)
          -- ∨ gt (succ b) (succ a)
          -- =>
          -- gt (succ a) (succ b) ∨ gt (succ b) (succ a)
          right

          -- Izquierda de conjuncion
          -- gt (succ a) (succ b) ∨ gt (succ b) (succ a)
          -- =>
          -- gt (succ a) (succ b)
          left

          constructor

          · /- ge (succ a) (succ b) -/

            -- Existe (succ zero) que resuelve "ge"
            -- ge (succ a) (succ b)
            -- =>
            -- succ a = add (succ b) (succ zero)
            exists (Nt.succ Nt.zero)

            -- Adicion de sucesor por la derecha
            -- succ a = add (succ b) (succ zero)
            -- =>
            -- succ a = succ (add (succ b) zero)
            rw [add_succ_right]

            -- Sucesor funcion
            -- succ a = succ (add (succ b) zero)
            -- =>
            -- a = add (succ b) zero
            apply succ_func

            -- Adicion de zero por la derecha
            -- a = add (succ b) zero
            -- =>
            -- a = succ b
            rw [add_zero_right]

            -- Hipotesis (h_eq : a = succ b)
            exact h_eq

          · /- succ a = succ b → False -/

            -- Hipotesis (h_eq : a = succ b)
            -- succ a = succ b
            -- =>
            -- succ a = a
            rw [← h_eq]

            -- Adicion de zero por la derecha
            -- succ a = a
            -- =>
            -- add (succ a) zero = a
            rw [← add_zero_right (Nt.succ a)]

            -- Adicion de sucesor por la izquierda
            -- add (succ a) zero = a
            -- succ (add a zero) = a
            rw [add_succ_left]

            -- Adicion de sucesor por la derecha
            -- succ (add a zero) = a
            -- =>
            -- add a (succ zero) = a
            rw [← add_succ_right]

            -- Adicion de cero por la derecha
            -- add a (succ zero) = a
            -- =>
            -- add a (succ zero) = add a zero
            rw [← add_zero_right a]

            -- Adicion de constante por la izquierda
            -- add a (succ zero) = add a zero
            -- =>
            -- succ zero = zero
            apply ne_add_const_left

            -- Sucesor no cero
            apply succ_ne_zero

        · /- (h_gt1 : gt a (succ b)) -/

          -- Separar conjuncion de hipotesis hge y hne
          -- (hge : ge a (succ b))
          -- =>
          -- (hne : a succ b)
          obtain ⟨hge, hne⟩ := h_gt1

          -- Obtener c desde hipotesis (hge : ge a (succ b))
          -- (h_gt1 : gt a (suss b))
          -- =>
          -- (h_gt1 : gt (add (succ b) c) (succ b))
          obtain ⟨c, rfl⟩ := hge

          -- Derecha de conjuncion
          -- succ a = succ b ∨ gt (succ a) (succ b)
          -- ∨ gt (succ b) (succ a)
          -- =>
          -- gt (succ a) (succ b) ∨ gt (succ b) (succ a)
          right

          -- Izquierda de conjuncion
          -- gt (succ a) (succ b) ∨ gt (succ b) (succ a)
          -- =>
          -- gt (succ a) (succ b)
          left

          constructor

          · /- ge (succ (add (succ b) c) (succ b) -/

            -- Existe (succ c) que resuelve "ge"
            -- ge (succ (add (succ b) c) (succ b)
            -- =>
            -- succ (add (succ b) c) = add (succ b) (succ c)
            exists (Nt.succ c)

            -- Adicion de sucesor por la derecha
            -- succ (add (succ b) c) = add (succ b) (succ c)
            -- =>
            -- add (succ b) (succ c) = add (succ b) (succ c)
            -- rw [← add_succ_right]

          · /- succ (add (succ b) c) = succ b -/

            -- Adicion de sucesor por la derehca
            -- succ (add (succ b) c) ≠ succ b
            -- =>
            -- add (succ b) (succ c) ≠ succ b
            rw [← add_succ_right]

            -- Adicion de zero por la derecha
            -- add (succ b) (succ c) ≠ succ b
            -- =>
            -- add (succ b) (succ c) ≠ add (succ b) zero
            conv =>
              rhs
              rw [← add_zero_right (Nt.succ b)]

            -- Adicion de constante
            -- add (succ b) (succ c) ≠ add (succ b) zero
            -- =>
            -- succ c ≠ zero
            apply ne_add_const_left

            -- Sucesro distinto de zero
            apply succ_ne_zero

        · /- (h_gt2 : gt (succ b) a) -/

          -- Separar hipotesis de gt
          -- (hne_succ : none)
          -- =>
          -- (hne_succ : succ b = a → False)
          -- (hge_succ : none)
          -- =>
          -- (hge_succ : succ b = a → False)
          obtain ⟨hge_succ, hne_succ⟩ := h_gt2

          -- Tercero excluido de igualdad a con b
          by_cases h : b = a

          · /- b = a -/

            -- Izquierda de conjuncion
            -- succ a = succ b ∨ gt (succ a) (succ b)
            -- ∨ gt (succ b) (succ a)
            -- =>
            -- succ a = succ b
            left

            -- Sucesor funcion
            -- succ a = succ b
            -- =>
            -- a = b
            apply succ_func

            -- Equivalencia simetrica
            -- a = b
            -- =>
            -- b = a
            replace h := Eq.symm h

            -- Calzar con h
            exact h

          · /- b ≠ a -/

            -- Derecha de conjuncion
            -- succ a = succ b ∨ gt (succ a) (succ b)
            -- ∨ gt (succ b) (succ a)
            -- =>
            -- gt (succ a) (succ b) ∨ gt (succ b) (succ a)
            right

            -- Izquierda de conjuncion
            -- gt (succ a) (succ b) ∨ gt (succ b) (succ a)
            -- =>
            -- gt (succ b) (succ a)
            right

            constructor

            · /- ge (succ b) (succ a) -/

              -- Obener "c" desde "ge"
              -- succ b = add a c
              -- =>
              -- (hne_succ : add a c ≠ a)
              obtain ⟨c, hcb_succ⟩ := hge_succ

              -- Hipotesis (hdb_succ : succ b = add a c)
              -- (hne_succ : succ b ≠ a)
              -- =>
              -- (hne_succ : add a c ≠ a)
              rw [hcb_succ] at hne_succ

              -- Adicion de zero por la derecha
              -- (hne_succ : add a c ≠ a)
              -- =>
              -- (hne_succ : add a c ≠ add a zero)
              rw [← add_zero_right a] at hne_succ

              -- Cancelacion de constante por la izquierda
              -- (hne_succ : add a c ≠ add a zero)
              -- =>
              -- (hne_succ : c = zero → False)
              replace hne_succ := ne_add_canc_left hne_succ

              -- Obtener antecesor
              -- (hdc : none)
              -- =>
              -- (hdc : succ d = c)
              have ⟨d, hdc, hdu⟩ := unique_ante hne_succ

              -- Hipotesis (hdc : c = succ d)
              -- (hcb_succ: succ b = add a c)
              -- =>
              -- (hcb_succ: succ b = add a (succ d))
              rw [← hdc] at hcb_succ

              -- Adicion de sucesor por la derecha
              -- (hcb_succ: succ b = add a (succ d))
              -- =>
              -- (hcb_succ: succ b = succ (add a d))
              rw [add_succ_right] at hcb_succ

              -- (hcb_succ: b = add a d)
              replace hcb_succ := succ_inj hcb_succ

              exists d

              rw [add_succ_left]
              rw [succ_func]

              exact hcb_succ

            · /- succ b ≠ succ a -/

              -- Hipotesis implicancia a hipotesis de teorema
              -- (h_succ : none)
              -- =>
              -- (h_succ : succ b = succ a)
              -- succ b = succ a → False
              -- =>
              -- False
              intro h_succ

              -- Aplicar desigualdad de h
              -- False
              -- =>
              -- b = a
              apply h

              -- Sucesor injectivo
              -- (h_succ : succ b = succ a)
              -- =>
              -- (h_succ : b = a)
              replace h_succ := succ_inj h_succ

              -- Calzar h_succ
              -- b = a
              -- =>
              -- True
              exact h_succ

theorem gt_ne_zero (a : Nt) : gt Nt.zero a → False := by
    -- Hipotesis implicancia a hipotesis de teorema
    -- (h : none)
    -- =>
    -- (h : gt zero a)
    intro h

    induction a with

    | zero =>

      -- Separar hipotesis desde h
      -- (hge : none)
      -- =>
      -- (hge : ge zero zero)
      -- (hne : none)
      -- =>
      -- (hne : zero ≠ zero)
      obtain ⟨hge, hne⟩ := h

      -- Hipotesis (hne: zero ≠ zero)
      -- False
      -- =>
      -- zero = zero
      apply hne

      -- Igualdad reflexiba
      -- zero = zero
      -- =>
      -- True
      rfl

    | succ a ih =>

      -- (ih : gt zero a → False)
      -- (h : gt zero (succ a))

      -- Separar hipotesis desde h
      -- (hge : none)
      -- =>
      -- (hge : ge zero (succ a)
      -- (hne : none)
      -- =>
      -- (hne : zero ≠ (succ a))
      obtain ⟨hge, hne⟩ := h

      -- Obtener "c" desde hge y guardad igualdad en heq
      -- (heq : none)
      -- =>
      -- (heq : zero = add (succ a) c)
      obtain ⟨c, heq⟩ := hge

      -- Hipotesis (ih : gt zero a → False)
      -- False
      -- =>
      -- gt zero a
      apply ih

      constructor
      · /- ge zero a -/

        -- Existe (succ c)
        -- ge zero a
        -- =>
        -- zero = add a (succ c)
        exists (Nt.succ c)

        -- Hipotesis (heq : zero = add (succ a) c)
        -- zero = add a (succ c)
        -- =>
        -- add (succ a) c = add a (succ c)
        rw [heq]

        -- Adicion de sucesor por la izquierda
        -- add (succ a) c = add a (succ c)
        -- =>
        -- succ (add a c) = add a (succ c)
        rw [add_succ_left]

        -- Adicion de sucesor por la derecha
        -- succ (add a c) = add a (succ c)
        -- =>
        -- succ (add a c) = succ (add a c)
        rw [add_succ_right]

      · /- zero ≠ a -/

        -- Hipotesis implicancia a hipotesis de teorema
        -- (hne: none);
        -- =>
        -- (hne: zero = a);
        -- zero ≠ a
        -- =>
        -- False
        intro hne

        -- Adicion de sucesor por la izquierda
        -- (heq : zero = add (succ a) c)
        -- =>
        -- (heq : zero = succ (add a c)
        rw [add_succ_left] at heq

        -- Sucesor distinto de cero
        -- False
        -- =>
        -- succ (add a c) = zero
        apply succ_ne_zero (add a c)

        -- Igualdad simétrica
        -- succ (add a c) = zero
        -- =>
        -- zero = succ (add a c)
        apply Eq.symm

        -- Calzar (heq : zero = succ (add a c)
        exact heq

theorem ge_zero_eq_zero (a : Nt) : ge Nt.zero a → Nt.zero = a := by

  -- ge zero a → zero = a
  -- =>
  -- zero = a
  intro hge

  by_cases hem : Nt.zero = a

  · /- zero = a -/

    -- Hipotesis (he : zero = a)
    -- zero = a
    -- =>
    -- True
    exact hem

  · /- zero ≠ a -/
    
    -- Conjugacion de hipotesis (hge : ge zero a) y (hem : zero = a)
    -- (hgt : none)
    -- =>
    -- (hgt : gt zero a)
    have hgt : gt Nt.zero a := ⟨hge, hem⟩

    -- Falso implica todo
    -- zero = a
    -- =>
    -- False
    exfalso

    -- Teorema (gt_ne_zero : gt zero a → False)
    -- False
    -- =>
    -- gt zero a
    apply gt_ne_zero

    -- Hipotesis (hgt : gt zero a)
    -- gt zero a
    -- =>
    -- True
    exact hgt

theorem gt_succ_then_ge {n m : Nt}
    (h : gt (Nt.succ n) m) : ge n m := by

    induction m with
    | zero =>

      -- Existe "n" que cumple (ge n m)
      -- ge n m
      -- =>
      -- n = add zero n
      exists n

      -- Simetria de la igualdad
      -- n = add zero n
      -- =>
      -- add zero n = n
      apply Eq.symm

      -- Matchear "add_zero_left"
      -- add zero n = n
      -- =>
      -- True
      exact add_zero_left n

    | succ m ih =>

      -- Separar hipotesis desde (h : gt (succ n) (succ m))
      -- (hne : none)
      -- =>
      -- (hne : succ n = succ m → False)
      -- (hgesucc : none)
      -- =>
      -- (hgesucc : ge (succ n) (succ m))
      obtain ⟨hgesucc, hne⟩ := h

      -- Obtener "c" que cumple (hgesucc: ge (succ n) (succ m))
      -- (hgesucc : none)
      -- =>
      -- (hgesucc : ge (succ n) (succ m))
      -- (hnsucc : none)
      -- =>
      -- (hnsucc : succ n = add (succ m) c)
      obtain ⟨c, hnsucc⟩ := hgesucc

      -- Hipotesis (hnsucc : succ n = add (succ m) c)
      -- (hne : succ n = succ m → False)
      -- =>
      -- (hne : add (succ m) c = succ m → False)
      rw [hnsucc] at hne

      -- Adicion de zero por la derecha
      -- (hne : add (succ m) c = succ m → False)
      -- =>
      -- (hne : add (succ m) c = add (succ m) zero → False)
      conv at hne => {
        rhs
        rw [← add_zero_right (Nt.succ m)]
      }

      -- Cancelacion de constante sumada por la izquierda
      -- (hne : add (succ m) c = add (succ m) zero → False)
      -- =>
      -- (hne : c = zero → False)
      replace hne := ne_add_canc_left hne

      -- Antecesor de "c" desde (hne : c = zero → False
      -- (hdc : none)
      -- =>
      -- (hdc : c = succ d)
      have ⟨d, hdc, hdu⟩ := unique_ante hne

      -- Existe "d" que cumple (objetivo : ge n (succ m))
      -- ge n (succ m)
      -- =>
      -- n = add (succ m) d
      exists d

      -- Adicion de sucesor por la izquierda
      -- n = add (succ m) d
      -- =>
      -- n = succ (add m d)
      rw [add_succ_left]

      -- Adicion de sucesor por la derecha
      -- n = succ (add m d)
      -- =>
      -- n = add m (succ d)
      rw [← add_succ_right]

      -- Hipotesis (hdc: c = succ d)
      -- n = add m (succ d)
      -- =>
      -- n = add m c
      rw [hdc]

      -- Adicion de sucesor por la izquierda
      -- (hnsucc : succ n = add (succ m) c)
      -- =>
      -- (hnsucc : succ n = succ (add m c))
      rw [add_succ_left] at hnsucc

      -- Sucesor injectivo
      -- (hnsucc : succ n = succ (add m c))
      -- =>
      -- (hnsucc : n = add m c)
      replace hnsucc := succ_inj hnsucc

      -- Calzar hipotesis (hnsucc : n = add m c)
      -- n = add m c
      -- =>
      -- True
      exact hnsucc

theorem strong_induction {P : Nt → Prop} {m0 : Nt}
    (h : ∀ n, ge n m0 → (∀ m, ge m m0 → gt n m → P m) → P n) :
    ∀ n, ge n m0 → P n := by

    let Q : Nt → Prop := fun n => ∀ m, ge m m0 → ge n m → P m

    have H : ∀ n, ge n m0 → Q n := by

      -- Hipotesis hgenm0 en implicancia a teorema
      -- ∀ n, ge n m0 → ∀ m, ge m m0 → ge n m → P m
      -- =>
      -- ∀ m, ge m m0 → ge n m → P m
      intro n hgenm0

      induction n with

      | zero =>

        -- Hipotesis hgemm0 y hgenm en implicancia a teorema
        -- ∀ m, ge m m0 → ge zero m → P m
        -- =>
        -- P m
        intro m hgemm0 hgenm

        have hQgt : ∀ m, ge m m0 → gt Nt.zero m → P m := by

          -- Hipotesis de implicancia a hipotesis de teorema
          -- (hgt : gt zero m)
          -- ∀ m, ge m m0 → gt zero m → P m
          -- P m
          intro m _ hgt

          -- Falso implica todo
          -- Pm
          -- =>
          -- False
          exfalso

          have hgt_ne_zero := gt_ne_zero m

          -- Teorema (hgt_ne_zero : gt zero m)
          -- False
          -- =>
          -- gt zero m
          apply hgt_ne_zero

          -- Calzar (hgt : gt zero m)
          -- gt zero m
          -- =>
          -- True
          exact hgt

        -- Instanciacion de h segun "n" y "hgenm0"
        -- (h : ∀ n, ge n m0 → (∀ m, ge m m0 → gt n m → P m) → P zero)
        -- =>
        -- (h : (∀ m, ge m m0 → gt zero m → P m) → P zero)
        replace h := h Nt.zero hgenm0

        -- Hipotesis (hm : ∀ m, ge m m0 → gt zero m → P m)
        -- (h : (∀ m, ge m m0 → gt zero m → P m) → P zero)
        -- =>
        -- (h : P zero)
        replace h := h hQgt

        -- Teorema (ge_zero_eq_zero : ge zero m → zero = m)
        -- (hzerom : none)
        -- =>
        -- (hzerom : zero = m)
        have hzerom := ge_zero_eq_zero m hgenm

        -- Hipotesis (hzerom : zero = m)
        -- P m
        -- =>
        -- P zero
        rw [← hzerom]

        -- Hipotesis (h : P zero)
        -- P zero
        -- =>
        -- True
        exact h

      | succ n ih =>

        -- Hipotesis (h : ∀ n, ge n m0 →
        --     (∀ m, ge m m0 → gt n m → P m) → P n)
        --
        -- (h : ∀ n, ge n m0 → (∀ m, ge m m0 → gt n m → P m) → P n)
        -- =>
        -- (h : (∀ m, ge m m0 → gt (succ n) m → P m) → P (succ n))
        replace h := h (Nt.succ n) hgenm0

        have hQgt : ∀ m, ge m m0 → gt (Nt.succ n) m → P m := by

            -- Hipotesis de implicancia a hipotesis de teorema
            -- (hgemm0 : none)
            -- =>
            -- (hgemm0 : ge m m0)
            -- (hgtsuccnm : none)
            -- =>
            -- (hgtsuccnm : gt (succ n) m)
            -- ∀ m, ge m m0 → gt (succ n) m → P m
            -- =>
            -- P m
            intro m hgemm0 hgtsuccnm

            -- Mayor implica mayor o igual
            -- (hgenm : none)
            -- =>
            -- (hgenm : ge n m)
            have hgenm := gt_succ_then_ge hgtsuccnm

            -- Transitividad de mayor o igual
            -- (hgenm0 : none)
            -- =>
            -- (hgenm0 : ge n m0)
            have hgenm0 := ge_trans hgenm hgemm0

            -- Hipotesis (ih : ge n m0 → Q n)
            -- P m
            -- =>
            -- True
            apply ih hgenm0 m hgemm0 hgenm

        -- Hipotesis (h :
        --  (∀ m, ge m m0 → gt (succ n) m → P m) → P (succ n))
        --
        -- (hn_succ : none)
        -- =>
        -- (hn_succ : P (succ n))
        have hn_succ := h hQgt

        have hQ : ∀ m, ge m m0 → ge (Nt.succ n) m → P m := by

            -- Hipotesis de implicancia a hipotesis de teorema
            -- (hgemm0 : none)
            -- =>
            -- (hgemm0 : ge m m0)
            -- (hgesuccnm : none)
            -- =>
            -- (hgesuccnm : ge (succ n) m)
            -- ∀ m, ge m m0 → ge (succ n) m → P m
            -- =>
            -- P m
            intro m hgemm0 hgesuccnm

            -- Tercero excluido igualdad entre "succ n" y "m"
            -- (hsuccnm : none)
            -- =>
            -- (hsuccnm : succ n = m)
            by_cases hsuccnm : Nt.succ n = m

            · /- succ n = m -/

              -- Hipotesis (hsuccnm : succ n = m)
              -- P m
              -- =>
              -- P (succ n)
              rw [← hsuccnm]

              -- Calzar hipotesis (hn_succ : P (succ n))
              -- P (succ n)
              -- =>
              -- True
              exact hn_succ

            · /- succ n = m → False -/

              -- Definicion de mayor
              -- (hgtsuccnm : none)
              -- =>
              -- (hgtsuccnm : gt (succ n) m)
              have hgtsuccnm : gt (Nt.succ n) m := ⟨hgesuccnm, hsuccnm⟩

              -- Sucesor mayor implica mayor o igual
              -- (hgenm : none)
              -- =>
              -- (hgenm : ge n m)
              have hgenm := gt_succ_then_ge hgtsuccnm

              -- Mayor o igual transitivo
              -- (hgenm0 : none)
              -- =>
              -- (hgenm0 : ge n m0)
              have hgenm0 := ge_trans hgenm hgemm0

              -- Hipotesis (ih : ge n m0 → Q n)
              -- P m
              -- =>
              -- True
              apply ih hgenm0 m hgemm0 hgenm

        exact hQ

    -- Hipotesis hgenm0 en implicancia a teorema
    -- ∀ n, ge n m0 → P n
    -- =>
    -- P n
    intro n hgenm0

    -- Hipotesis (H : (n : Nt), ge n m0 → Q n)
    -- P n
    -- =>
    -- True
    apply H n hgenm0 n hgenm0 (ge_refl n)

theorem backward_induction {P : Nt → Prop} {n : Nt}
    (h : ∀ m, P (Nt.succ m) → P m) (hn : P n) :
    ∀ m, ge n m → P m := by

    intro m hgenm

    induction n with
    | zero =>

      -- zero = m
      replace hgenm := ge_zero_eq_zero m hgenm

      rw [← hgenm]

      exact hn

    | succ n ih =>

      -- (ih : ge n m → P m

      by_cases hsuccnm : Nt.succ n = m

      · /- succ n = m -/

        rw [← hsuccnm]

        exact hn

      · /- succ n = m → False -/

        replace hn := h n hn

        have gtsuccnm : gt (Nt.succ n) m := ⟨hgenm, hsuccnm⟩

        replace hgenm := gt_succ_then_ge gtsuccnm

        apply ih hn hgenm

