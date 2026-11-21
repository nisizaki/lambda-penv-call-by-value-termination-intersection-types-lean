import LambdaPEnvCBV.Completeness

/-!
# Soundness: `Typ M → CFN M`

Port of `Soundness.thy` (call-by-value λpenv).  Adapted from the Lean ports of
call-by-value λenv and of call-by-name λpenv (name types).

Adaptations: sets of terms `trm set` are predicates `Trm → Prop`, so `M ∈ I A` is `I A M`.
`I` is defined by well-founded recursion on the size of the type.  The clause `I (QN x)` is
`Star cbv M (nm x)`; in the `Env` clause the name-application condition quantifies over
`N` with `Star cbv N (nm x)` directly.
-/

namespace LambdaPEnvCBV

open Trm Ty

/-! ## Normal forms of some shapes -/

theorem NF_Var (x : Var) : NF (var x) := by
  rintro b (h | h) <;> cases h

theorem NF_App_inert {I F : Trm} (i : inert I) (ni : NF I) (f : fb F) (nf : NF F)
    (nn : ∀ y, F ≠ nm y) : NF (app I F) := by
  rintro Q (h | h)
  · cases h with
    | AppConst _ x => exact nn x rfl
    | AppL _ h => exact ni _ (Or.inl h)
    | AppR _ h => exact nf _ (Or.inl h)
  · cases h with
    | Beta1 => exact absurd i (not_inert_Clo _ _ _)
    | Beta2 => exact absurd i (not_inert_Lam _ _)
    | AppL _ b => exact ni _ (Or.inr b)
    | AppR _ b => exact nf _ (Or.inr b)

theorem NF_Comp_inert {I : Trm} (x : Var) (i : inert I) (ni : NF I) : NF (comp (var x) I) := by
  rintro Q (h | h)
  · cases h with
    | IdR => exact absurd i not_inert_Id
    | VarRef => exact absurd i (not_inert_Extn _ _ _)
    | VarSkip _ _ _ => exact absurd i (not_inert_Extn _ _ _)
    | CompL _ h => exact sig_Var_no _ _ h
    | CompR _ h => exact ni _ (Or.inl h)
  · cases h with
    | VarR _ b => exact ni _ (Or.inr b)
    | VarClos => exact absurd i (not_inert_Clo _ _ _)
    | VarLam => exact absurd i (not_inert_Lam _ _)

theorem CFN_Nm (x : Var) : CFN (nm x) := ⟨nm x, .refl _, NF_Nm x, .FNm x⟩

theorem CFN_QN {N : Trm} {x : Var} (h : Star cbv N (nm x)) : CFN N :=
  CFN_back_steps h (CFN_Nm x)

theorem cbv_AppConst (M : Trm) (x : Var) : cbv (app M (nm x)) (comp (var x) M) :=
  sig_imp_cbv (.AppConst M x)

theorem CFN_sig_fb {M : Trm} (f : fb M) : CFN M := by
  obtain ⟨N, s, n⟩ := sig_nf M
  have fN : fb N := sig_steps_fb s f
  exact ⟨N, sig_steps_cbv s, fb_NF fN n, fN⟩

theorem CFN_Lam (x : Var) (M : Trm) : CFN (lam x M) := CFN_sig_fb (.FLam x M)
theorem CFN_Extn (M : Trm) (x : Var) (N : Trm) : CFN (extn M x N) := CFN_sig_fb (.FExtn M x N)
theorem CFN_Clo (x : Var) (M e : Trm) : CFN (comp (lam x M) e) := CFN_sig_fb (.FClo x M e)
theorem CFN_Id : CFN iden := CFN_sig_fb .FId

/-- Weak neutral terms. -/
inductive wneu : Trm → Prop where
  | wneu_var (x : Var) : wneu (var x)
  | wneu_app {M : Trm} (N : Trm) : wneu M → CFN N → wneu (app M N)
  | wneu_comp {M : Trm} (x : Var) : wneu M → wneu (comp (var x) M)

theorem wneu_reduces {M : Trm} (h : wneu M) : ∃ I, Star cbv M I ∧ NF I ∧ inert I := by
  induction h with
  | wneu_var x => exact ⟨var x, .refl _, NF_Var x, .IVar x⟩
  | wneu_app N _ hN ih =>
    obtain ⟨I, r1, n1, i⟩ := ih
    obtain ⟨F, r2, n2, f⟩ := hN
    have r3 : Star cbv (app _ N) (app I F) :=
      (cbv_steps_AppL N r1).trans (cbv_steps_AppR (.FInert i) r2)
    by_cases hy : ∃ y, F = nm y
    · obtain ⟨y, rfl⟩ := hy
      exact ⟨comp (var y) I, r3.tail (cbv_AppConst I y), NF_Comp_inert y i n1, .IComp y i⟩
    · have nn : ∀ y, F ≠ nm y := fun y h => hy ⟨y, h⟩
      exact ⟨app I F, r3, NF_App_inert i n1 f n2 nn, .IApp i f⟩
  | wneu_comp x _ ih =>
    obtain ⟨I, r1, n1, i⟩ := ih
    exact ⟨comp (var x) I, cbv_steps_VarR x r1, NF_Comp_inert x i n1, .IComp x i⟩

theorem wneu_CFN {M : Trm} (h : wneu M) : CFN M := by
  obtain ⟨I, r, n, i⟩ := wneu_reduces h
  exact ⟨I, r, n, .FInert i⟩

/-! ## Interpretation of types -/

theorem Ty.ind {P : Ty → Prop}
    (tv : ∀ n, P (TV n)) (om : P Om) (arr : ∀ A B, P A → P B → P (Arr A B))
    (inter : ∀ A B, P A → P B → P (Ty.Inter A B))
    (env : ∀ m ob, (∀ x A, (x, A) ∈ m → P A) → P (Env m ob))
    (qn : ∀ x, P (QN x)) : ∀ A, P A
  | TV n => tv n
  | Om => om
  | Arr A B => arr A B (Ty.ind tv om arr inter env qn A) (Ty.ind tv om arr inter env qn B)
  | Ty.Inter A B =>
      inter A B (Ty.ind tv om arr inter env qn A) (Ty.ind tv om arr inter env qn B)
  | Env m ob => env m ob (fun x A h => Ty.ind tv om arr inter env qn A)
  | QN x => qn x
termination_by A => sizeOf A
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (have h1 := List.sizeOf_lt_of_mem h; simp at h1; omega)

/-- Realizability interpretation of types (Isabelle `I`; a set of terms is a predicate). -/
def I : Ty → Trm → Prop
  | TV _, M => CFN M
  | Om, _ => True
  | Arr A B, M => CFN M ∧ ∀ N, I A N → CFN N → I B (app M N)
  | Ty.Inter A B, M => I A M ∧ I B M
  | QN x, M => Star cbv M (nm x)
  | Env m ob, e =>
      ((m ≠ [] ∨ ob = true) → CFN e) ∧
      ∀ p (hp : p ∈ m), map_of m p.1 = some p.2 →
        I p.2 (comp (var p.1) e) ∧ ∀ N, Star cbv N (nm p.1) → I p.2 (app e N)
termination_by A => sizeOf A
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (obtain ⟨a, b⟩ := p; have h1 := List.sizeOf_lt_of_mem hp; simp at h1 ⊢; omega)

theorem I_TV (n : Nat) (M : Trm) : I (TV n) M = CFN M := by rw [I]
theorem I_Om (M : Trm) : I Om M = True := by rw [I]
theorem I_Arr (A B : Ty) (M : Trm) :
    I (Arr A B) M = (CFN M ∧ ∀ N, I A N → CFN N → I B (app M N)) := by rw [I]
theorem I_Inter (A B : Ty) (M : Trm) : I (Ty.Inter A B) M = (I A M ∧ I B M) := by rw [I]
theorem I_QN (x : Var) (M : Trm) : I (QN x) M = Star cbv M (nm x) := by rw [I]

theorem I_Env {m : List (Var × Ty)} {ob : Bool} {e : Trm} :
    I (Env m ob) e ↔
      ((m ≠ [] ∨ ob = true) → CFN e) ∧
      (∀ x A, map_of m x = some A →
        I A (comp (var x) e) ∧ ∀ N, Star cbv N (nm x) → I A (app e N)) := by
  rw [I]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨h1, fun x A hA => h2 (x, A) (map_of_SomeD hA) hA⟩
  · intro ⟨h1, h2⟩
    exact ⟨h1, fun p _ hp => h2 p.1 p.2 hp⟩

theorem I_back {M M' : Trm} {A : Ty} (h : cbv M M') (hI : I A M') : I A M := by
  induction A using Ty.ind generalizing M M' with
  | tv n => rw [I_TV] at *; exact CFN_back h hI
  | om => rw [I_Om]; trivial
  | arr A B _ ihB =>
    rw [I_Arr] at *
    exact ⟨CFN_back h hI.1, fun N hN cN => ihB (cbv_AppL N h) (hI.2 N hN cN)⟩
  | inter A B ihA ihB =>
    rw [I_Inter] at *
    exact ⟨ihA h hI.1, ihB h hI.2⟩
  | env m ob ih =>
    rw [I_Env] at *
    exact ⟨fun hm => CFN_back h (hI.1 hm), fun x A l =>
      ⟨ih x A (map_of_SomeD l) (cbv_VarR x h) (hI.2 x A l).1,
       fun N hN => ih x A (map_of_SomeD l) (cbv_AppL N h) ((hI.2 x A l).2 N hN)⟩⟩
  | qn x => rw [I_QN] at *; exact .step h hI

theorem I_back_steps {M M' : Trm} {A : Ty} (h : Star cbv M M') (hI : I A M') : I A M := by
  induction h with
  | refl => exact hI
  | step h _ ih => exact I_back h (ih hI)

theorem I_fwd {M M' : Trm} {A : Ty} (h : cbv M M') (hI : I A M) : I A M' := by
  induction A using Ty.ind generalizing M M' with
  | tv n => rw [I_TV] at *; exact CFN_fwd h hI
  | om => rw [I_Om]; trivial
  | arr A B _ ihB =>
    rw [I_Arr] at *
    exact ⟨CFN_fwd h hI.1, fun N hN cN => ihB (cbv_AppL N h) (hI.2 N hN cN)⟩
  | inter A B ihA ihB =>
    rw [I_Inter] at *
    exact ⟨ihA h hI.1, ihB h hI.2⟩
  | env m ob ih =>
    rw [I_Env] at *
    exact ⟨fun hm => CFN_fwd h (hI.1 hm), fun x A l =>
      ⟨ih x A (map_of_SomeD l) (cbv_VarR x h) (hI.2 x A l).1,
       fun N hN => ih x A (map_of_SomeD l) (cbv_AppL N h) ((hI.2 x A l).2 N hN)⟩⟩
  | qn x => rw [I_QN] at *; exact Nm_fwd h hI

theorem I_fwd_steps {M M' : Trm} {A : Ty} (h : Star cbv M M') (hI : I A M) : I A M' := by
  induction h with
  | refl => exact hI
  | step h _ ih => exact ih (I_fwd h hI)

theorem I_ess {A : Ty} (hA : ess A) {M : Trm} (hI : I A M) : CFN M := by
  induction A using Ty.ind generalizing M with
  | tv n => rwa [I_TV] at hI
  | om => exact absurd hA (by simp [ess])
  | arr A B _ _ => rw [I_Arr] at hI; exact hI.1
  | inter A B ihA ihB =>
    rw [I_Inter] at hI
    rcases hA with h | h
    · exact ihA h hI.1
    · exact ihB h hI.2
  | env m ob _ => rw [I_Env] at hI; exact hI.1 hA
  | qn x => rw [I_QN] at hI; exact CFN_QN hI

theorem qfree_of_mem {m : List (Var × Ty)} (h : qfree.qfreeList m) {x : Var} {A : Ty}
    (hx : (x, A) ∈ m) : qfree A := by
  induction m with
  | nil => cases hx
  | cons p m ih =>
    obtain ⟨y, B⟩ := p
    simp only [qfree.qfreeList] at h
    rcases List.mem_cons.mp hx with e | e
    · cases e; exact h.1
    · exact ih h.2 e

theorem wneu_I {A : Ty} (hq : qfree A) {M : Trm} (hw : wneu M) : I A M := by
  induction A using Ty.ind generalizing M with
  | tv n => rw [I_TV]; exact wneu_CFN hw
  | om => rw [I_Om]; trivial
  | arr A B _ ihB =>
    rw [I_Arr]; exact ⟨wneu_CFN hw, fun N _ cN => ihB hq.2 (.wneu_app N hw cN)⟩
  | inter A B ihA ihB => rw [I_Inter]; exact ⟨ihA hq.1 hw, ihB hq.2 hw⟩
  | env m ob ih =>
    rw [I_Env]
    refine ⟨fun _ => wneu_CFN hw, fun x A l => ?_⟩
    have q : qfree A := qfree_of_mem hq (map_of_SomeD l)
    exact ⟨ih x A (map_of_SomeD l) q (.wneu_comp x hw),
      fun N hN => ih x A (map_of_SomeD l) q (.wneu_app N hw (CFN_QN hN))⟩
  | qn x => exact absurd hq (by simp [qfree])

theorem Var_I (x : Var) {A : Ty} (hq : qfree A) : I A (var x) := wneu_I hq (.wneu_var x)

/-! ## Monotonicity -/

theorem I_mono {A B : Ty} (h : A ≼ B) : ∀ {M : Trm}, I A M → I B M := by
  induction h with
  | s_refl => exact id
  | s_trans _ _ ih1 ih2 => exact fun h => ih2 (ih1 h)
  | s_top => intro M _; rw [I_Om]; trivial
  | s_il => intro M h; rw [I_Inter] at h; exact h.1
  | s_ir => intro M h; rw [I_Inter] at h; exact h.2
  | s_glb _ _ ih1 ih2 => intro M h; rw [I_Inter]; exact ⟨ih1 h, ih2 h⟩
  | s_arr _ _ ih1 ih2 =>
    intro M h
    rw [I_Arr] at *
    exact ⟨h.1, fun N hN cN => ih2 (h.2 N (ih1 hN) cN)⟩
  | @s_env_core m' m ob' ob hdom hsub hob ih =>
    intro e he
    rw [I_Env] at he ⊢
    refine ⟨fun hm => he.1 ?_, fun x A' l => ?_⟩
    · rcases hm with hm | hm
      · cases m' with
        | nil => exact absurd rfl hm
        | cons p ps =>
          obtain ⟨x, A'⟩ := p
          obtain ⟨A, hA⟩ := hdom x A' (map_of_cons_self _ _ _)
          left
          intro e; subst e; simp [map_of] at hA
      · exact Or.inr (hob hm)
    · obtain ⟨A, hA⟩ := hdom x A' l
      have hh := he.2 x A hA
      exact ⟨ih x A' A l hA hh.1, fun N hN => ih x A' A l hA (hh.2 N hN)⟩
  | s_emeet m1 o1 m2 o2 =>
    intro e he
    rw [I_Inter, I_Env, I_Env] at he
    obtain ⟨⟨c1, l1⟩, ⟨c2, l2⟩⟩ := he
    rw [I_Env]
    refine ⟨fun hm => ?_, fun x A l => ?_⟩
    · rcases hm with hm | hm
      · by_cases h1 : m1 = []
        · apply c2; left; intro h2; apply hm; simp [emeet, h1, h2]
        · exact c1 (Or.inl h1)
      · cases o1 <;> cases o2 <;> simp_all
    · rw [map_of_emeet] at l
      cases h1 : map_of m1 x with
      | none =>
        rw [h1] at l
        exact l2 x A l
      | some A1 =>
        rw [h1] at l
        cases h2 : map_of m2 x with
        | none => rw [h2] at l; cases l; exact l1 x _ h1
        | some A2 =>
          rw [h2] at l; cases l
          have a1 := l1 x _ h1
          have a2 := l2 x _ h2
          rw [I_Inter]
          refine ⟨⟨a1.1, a2.1⟩, fun N hN => ?_⟩
          rw [I_Inter]; exact ⟨a1.2 N hN, a2.2 N hN⟩
  | s_omenv =>
    intro M _
    rw [I_Env]
    exact ⟨fun h => by simp at h, fun x A h => by simp [map_of] at h⟩
  | @s_envarr m x A ob hl =>
    intro e he
    rw [I_Env] at he
    rw [I_Arr]
    have hh := he.2 x A hl
    refine ⟨he.1 (Or.inl ?_), fun N hN _ => hh.2 N ?_⟩
    · intro e; subst e; simp [map_of] at hl
    · rwa [I_QN] at hN
  | s_arrenv x A =>
    intro M hM
    rw [I_Arr] at hM
    obtain ⟨cf, ap⟩ := hM
    have ap' : ∀ N, Star cbv N (nm x) → I A (app M N) := fun N hN =>
      ap N (by rw [I_QN]; exact hN) (CFN_QN hN)
    have c : I A (comp (var x) M) := I_fwd (cbv_AppConst M x) (ap' (nm x) (.refl _))
    rw [I_Env]
    refine ⟨fun _ => cf, fun y B l => ?_⟩
    by_cases hxy : x = y
    · subst hxy
      simp [map_of] at l
      subst l
      exact ⟨c, ap'⟩
    · simp [map_of, hxy] at l

/-! ## Realizers -/

theorem qfree_map_of {m : List (Var × Ty)} (q : ∀ p ∈ m, qfree p.2) {x : Var} {A : Ty}
    (l : map_of m x = some A) : qfree A := q (x, A) (map_of_SomeD l)

theorem Id_I {m : List (Var × Ty)} {ob : Bool} (q : ∀ p ∈ m, qfree p.2) :
    I (Env m ob) iden := by
  rw [I_Env]
  refine ⟨fun _ => CFN_Id, fun x A l => ?_⟩
  have c : I A (comp (var x) iden) :=
    I_back (sig_imp_cbv (.IdR _)) (Var_I _ (qfree_map_of q l))
  refine ⟨c, fun N hN => ?_⟩
  exact I_back_steps (cbv_steps_AppR .FId hN) (I_back (cbv_AppConst iden x) c)

theorem Extn_I {N e : Trm} {A : Ty} {m : List (Var × Ty)} {ob : Bool} {x : Var}
    (n : I A N) (e' : I (Env m ob) e) : I (Env ((x, A) :: m) ob) (extn N x e) := by
  rw [I_Env]
  refine ⟨fun _ => CFN_Extn _ _ _, fun y B l => ?_⟩
  have c : I B (comp (var y) (extn N x e)) := by
    by_cases h : x = y
    · subst h
      rw [map_of_cons_self] at l; cases l
      exact I_back (sig_imp_cbv (.VarRef _ _ _)) n
    · rw [map_of_cons_ne _ _ h] at l
      rw [I_Env] at e'
      exact I_back (sig_imp_cbv (.VarSkip _ _ h)) (e'.2 y B l).1
  exact ⟨c, fun N' hN' =>
    I_back_steps (cbv_steps_AppR (.FExtn _ _ _) hN') (I_back (cbv_AppConst _ y) c)⟩

/-! ## Basic lemma -/

def env_app (M e : Trm) : Trm := if e = iden then M else comp M e

theorem env_app_iden (M : Trm) : env_app M iden = M := by simp [env_app]
theorem env_app_ne {M e : Trm} (h : e ≠ iden) : env_app M e = comp M e := by simp [env_app, h]

theorem basic {C : Ty} {M : Trm} {A : Ty} (h : Hasty C M A) :
    ∀ {e : Trm}, I C e → I A (env_app M e) := by
  induction h with
  | @TVar C m ob x A h1 h2 =>
    intro e he
    have em := I_mono h1 he
    rw [I_Env] at em
    have c := (em.2 x A h2).1
    by_cases h : e = iden
    · subst h; rw [env_app_iden]; exact I_fwd (sig_imp_cbv (.IdR _)) c
    · rw [env_app_ne h]; exact c
  | @TLam C m ob x A M B h1 h2 ih =>
    intro e he
    have em : I (Env m ob) e := I_mono h1 he
    have fl : fb (env_app (lam x M) e) := by
      by_cases h : e = iden
      · subst h; rw [env_app_iden]; exact .FLam _ _
      · rw [env_app_ne h]; exact .FClo _ _ _
    rw [I_Arr]
    refine ⟨?_, fun N n cn => ?_⟩
    · by_cases h : e = iden
      · subst h; rw [env_app_iden]; exact CFN_Lam x M
      · rw [env_app_ne h]; exact CFN_Clo x M e
    · obtain ⟨F, r, nf, f⟩ := cn
      have nF : I A F := I_fwd_steps r n
      have key : I B (app (env_app (lam x M) e) F) := by
        by_cases h : e = iden
        · subst h
          rw [env_app_iden]
          have := ih (Extn_I nF em)
          rw [env_app_ne (by simp)] at this
          exact I_back (beta_imp_cbv (.Beta2 x M f)) this
        · rw [env_app_ne h]
          have := ih (Extn_I nF em)
          rw [env_app_ne (by simp)] at this
          exact I_back (beta_imp_cbv (.Beta1 x M e f)) this
      exact I_back_steps (cbv_steps_AppR fl r) key
  | @TApp C M A B N _ _ he ih1 ih2 =>
    intro e hI
    have m := ih1 hI
    have n := ih2 hI
    have cn : CFN (env_app N e) := I_ess he n
    rw [I_Arr] at m
    by_cases h : e = iden
    · subst h; rw [env_app_iden] at m n cn ⊢; exact m.2 _ n cn
    · rw [env_app_ne h] at m n cn ⊢
      have := m.2 _ n cn
      exact I_back (sig_imp_cbv (.DApp _ _ _)) this
  | TId C =>
    intro e he
    by_cases h : e = iden
    · subst h; rw [env_app_iden]; exact he
    · rw [env_app_ne h]; exact I_back (sig_imp_cbv (.IdL _)) he
  | @TExtn C M A N m ob x _ _ ih1 ih2 =>
    intro e he
    have m' := ih1 he
    have n := ih2 he
    by_cases h : e = iden
    · subst h; rw [env_app_iden] at m' n ⊢; exact Extn_I m' n
    · rw [env_app_ne h] at m' n ⊢
      exact I_back (sig_imp_cbv (.DExtn _ _ _ _)) (Extn_I m' n)
  | @TComp C N D M A _ _ ih1 ih2 =>
    intro e he
    by_cases h : e = iden
    · subst h
      have n : I D N := by have := ih1 he; rwa [env_app_iden] at this
      have := ih2 n
      rw [env_app_iden]
      by_cases hN : N = iden
      · subst hN
        rw [env_app_iden] at this
        exact I_back (sig_imp_cbv (.IdR _)) this
      · rwa [env_app_ne hN] at this
    · have n : I D (comp N e) := by have := ih1 he; rwa [env_app_ne h] at this
      have := ih2 n
      rw [env_app_ne (by simp)] at this
      rw [env_app_ne h]
      exact I_back (sig_imp_cbv (.Ass _ _ _)) this
  | TOm => intro _ _; rw [I_Om]; trivial
  | TInter _ _ ih1 ih2 => intro e he; rw [I_Inter]; exact ⟨ih1 he, ih2 he⟩
  | TSub _ hs ih => intro e he; exact I_mono hs (ih he)
  | TNm C x =>
    intro e he
    by_cases h : e = iden
    · subst h; rw [env_app_iden, I_QN]; exact .refl _
    · rw [env_app_ne h, I_QN]; exact .single (sig_imp_cbv (.ConstComp x e))

theorem soundness {M : Trm} (h : Typ M) : CFN M := by
  obtain ⟨m, ob, A, t, e, q⟩ := h
  have := basic t (Id_I (ob := ob) q)
  rw [env_app_iden] at this
  exact I_ess e this

end LambdaPEnvCBV
