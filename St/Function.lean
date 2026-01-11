import St.Axioms


/- Func definition -/

axiom Func : St → St → Type

axiom func_fromRel {A B : St} {P : St → St → Prop}
  (h_tot : ∀ x : St, mem x A → ∃ y, mem y B ∧ P x y)
  (h_uniq : ∀ x y1 y2 : St, mem x A → P x y1 → P x y2 → (y1 =st y2))
  : Func A B

axiom app {A B : St} : Func A B → St → St

axiom func_keepsRel {A B : St} {P : St → St → Prop}
  (h_tot : ∀ x : St, mem x A → ∃ y, mem y B ∧ P x y)
  (h_uniq : ∀ x y1 y2 : St, mem x A → P x y1 → P x y2 → (y1 =st y2))
  (x : St) (hx : mem x A) :

  P x (app (func_fromRel h_tot h_uniq) x)

