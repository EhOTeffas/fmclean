section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro np,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro p,
  by_contra,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
split,
  -- ¬¬P → P --
  intro p,
  by_contra,
  contradiction,
  -- P → ¬¬P --
  intro p,
  intro np,
  contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro hp,
  cases hp with hp hq,
  right,
  assumption,
  left,
  assumption,

end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro hp,
  cases hp with hp hq,
  split,
  assumption,
  assumption,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro hp,
  intro p,
  cases hp with hp p,
  contradiction,
  assumption,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro hp,
  intro p,
  cases hp with hp p,
  contradiction,
  assumption,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hp,
  intro q,
  intro p,
  have z := hp p,
  contradiction, 
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro hp,
  intro p,
  by_cases q: Q,
  assumption,
  have z:= hp q,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  -- (P → Q) → (¬Q → ¬P) --
  intro hp,
  intro q,
  intro p,
  have z := hp p,
  contradiction,
  -- (¬Q → ¬P) → (P → Q) -- 
  intro hp,
  intro p,
  by_cases q: Q,
  assumption,
  have z:= hp q,
  contradiction,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro p,
    have a : P∨¬P,
    right,
    intro hp,
      have b: P∨¬P,
      left, 
      assumption,
    contradiction,
  contradiction, 
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro p,
  intro hp,
  apply hp,
  apply p,
  intro q,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro a,
  intro b,
  cases b with bp bq,
  cases a with bp bq,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro a,
  intro b,
  cases a with q p, 
  cases b with nq np,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro a,
  split,
    intro p,
    apply a,
    left,
    assumption,

    intro q,
    apply a,
    right,
    assumption,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro a,
  intro b,
  cases a with np nq,
  cases b,
  contradiction,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro a,
  by_cases b: P,
  left,
  intro q,
  have c: P∧Q,
  split,
    assumption,
    assumption,
    contradiction,
    right,
    assumption,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro a,
  intro b,
  cases b with pp qq,
  cases a with nq np,
  contradiction,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  -- ¬(P∧Q) → (¬Q ∨ ¬P) --
intro a,
  by_cases b: P,
  left,
  intro q,
  have c: P∧Q,
  split,
    assumption,
    assumption,
    contradiction,
    right,
    assumption,
  -- (¬P ∨ ¬Q) → ¬(P∧Q) --
    intro a,
    intro b,
    cases b with pp qq,
    cases a with nq np,
    contradiction,
    contradiction,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  --   ¬(P∧Q) → (¬Q ∨ ¬P)   --
    intro a,
    split,
    intro p,
    apply a,
    left,
    assumption,

    intro q,
    apply a,
    right,
    assumption,
  -- (¬P ∧ ¬Q) → ¬(P∨Q)  --
    intro a,
    intro b,
    cases a with np nq,
    cases b,
    contradiction,
    contradiction,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro a,
  cases a with p q,
  cases q with pp qq,
  left,
  split,
  assumption,
  assumption,
  right,
  split,
  assumption,
  assumption,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro a,
  split,
    cases a with pq pr,
    cases pq with p q,
      assumption,
    cases pr with p r,
      assumption,
    cases a,
      cases a with p q,
      left,
      assumption,
      cases a with p r,
      right,
      assumption,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro a,
  split,
  cases a,
  left,
  assumption,
  cases a with q r,
  right,
  assumption,
  cases a,
  left, 
  assumption,
  cases a with q r,
  right,
  assumption,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro a,
  cases a with pq pr,
  cases pr with p r,
  cases pq with pp q,
  left,
  assumption,
  left,
  assumption,
  cases pq with p q,
  left,
  assumption,
  right,
  split,
  assumption,
  assumption,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro a,
  intro p,
  intro q,
  apply a,
  split,
  assumption,
  assumption,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro a,
  intro b,
  cases b,
  apply a,
  assumption,
  assumption,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro a,
  assumption,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro a,
  left,
  assumption,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro a,
  right,
  assumption,   
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro a,
  cases a with p q,
  assumption,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro a,
  cases a with p q,
  assumption,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro a,
  cases a,
  assumption,
  intro a,
  split,
  assumption, 
  assumption,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro a,
  cases a,
  assumption,
  assumption,
  intro b,
  right,
  assumption,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro a,
  intro b,
  intro pb,
  apply a,
  existsi b,
  assumption,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro a,
  intro b,
  cases b with c d,
  apply a c,
  assumption,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro a,
  by_contra b,
  apply a,
  intro c,
  by_contra d,
  apply b,
  existsi c,
  assumption,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro a,
  cases a with b c,
  intro d,
  have := d b,
  contradiction,
end

theorem demorgan_forall_law : 
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
split,
  --  ¬(∀x, P x) → (∃x, ¬P x)  --
  intro a,
  by_contra b,
  apply a,
  intro c,
  by_contra d,
  apply b,
  existsi c,
  assumption,
  -- (∃x, ¬P x) → ¬(∀x, P x)  --
  intro a,
  cases a with b c,
  intro d,
  have := d b,
  contradiction,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  -- ¬(∃x, P x) → (∀x, ¬P x) --
  intro a,
  intro b,
  intro pb,
  apply a,
  existsi b,
  assumption,
  -- (∀x, ¬P x) → ¬(∃x, P x) --
  intro a,
  intro b,
  cases b with c d,
  apply a c,
  assumption,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro a,
  cases a with b c,
  intro d,
  have x := d b,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro a, 
  intro b,
  cases b with c d,
  have x := a c,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro a, 
  intro b,
  by_contra c,
  apply a,
  existsi b,
  assumption,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro a,
  by_contra b,
  apply a,
  intro c,
  intro d,
  apply b,
  existsi c,
  assumption,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  --  (∀x, P x) → ¬(∃x, ¬P x) --
  intro a, 
  intro b,
  cases b with c d,
  have x := a c,
  contradiction,
  -- ¬(∃x, ¬P x) → (∀x, P x) --
  intro a, 
  intro b,
  by_contra c,
  apply a,
  existsi b,
  assumption,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  -- (∃x, P x) → ¬(∀x, ¬P x) --
  intro a,
  cases a with b c,
  intro d,
  have x := d b,
  contradiction,
  -- ¬(∀x, ¬P x) → (∃x, P x) --
  intro a,
  by_contra b,
  apply a,
  intro c,
  intro d,
  apply b,
  existsi c,
  assumption,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro a,
  cases a with b c,
  cases c with d e,
  split,
  existsi b,
  assumption,
  existsi b,
  assumption,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro a,
  cases a with b c,
  cases c with d e,
  left,
  existsi b,
  assumption,
  right,
  existsi b,
  assumption,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro a,
  cases a with b c,
  cases b with d e,
  existsi d,
  left,
  assumption,
  cases c with x y,
  existsi x,
  right,
  assumption,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro a,
  split,
  intro b,
  have x:= a b,
  cases x,
  assumption,
  intro c,
  have y:= a c,
  cases y,
  assumption,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro a,
  cases a with a b,
  intro c,
  split,
  have x:= a c,
  assumption,
  have y:= b c,
  assumption,
  
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro a,
  intro c,
  cases a with a b,
  have x:= a c,
  left, 
  assumption,
  have y:= b c,
  right,
  assumption,
  
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate