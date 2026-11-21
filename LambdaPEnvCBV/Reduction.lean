import LambdaPEnvCBV.Sigma

/-!
# Call-by-value reduction: full σ plus left-to-right β_v

Port of `Reduction.thy`.

Fireballs (in the sense of open call-by-value) are values and inert terms.  Values are
abstractions, closures, `id` and environment extensions; the components of closures and
extensions are not evaluated (environments are lazy).  Inert terms are variables,
applications of inert terms to fireballs, and variable look-ups in inert environments.
No σ-normality is required.

The argument of a β_v-redex must be a fireball.  β_v works in the function part of an
application, in the argument once the function part is a fireball, and in the environment
of a variable look-up (`VarR`).  It does not work under λ, inside environment extensions or
closure environments, or on the left of a composition.

Adaptation: Isabelle's `inductive inert and fb` is a Lean `mutual` pair of inductive
predicates; `M →β N` is `beta M N`, `M →v N` is `cbv M N`, `M →v* N` is `Star cbv M N`.
-/

namespace LambdaPEnvCBV

open Trm

/-! ## Fireballs -/

mutual
inductive inert : Trm → Prop where
  | IVar (x : Var) : inert (var x)
  | IApp {M N : Trm} : inert M → fb N → inert (app M N)
  | IComp {M : Trm} (x : Var) : inert M → inert (comp (var x) M)

inductive fb : Trm → Prop where
  | FInert {M : Trm} : inert M → fb M
  | FLam (x : Var) (M : Trm) : fb (lam x M)
  | FClo (x : Var) (M L : Trm) : fb (comp (lam x M) L)
  | FId : fb iden
  | FExtn (M : Trm) (x : Var) (L : Trm) : fb (extn M x L)
  | FNm (x : Var) : fb (nm x)
end

theorem fb_Var (x : Var) : fb (var x) := .FInert (.IVar x)

theorem inert_App_iff {M N : Trm} : inert (app M N) ↔ inert M ∧ fb N := by
  constructor
  · intro h; cases h with
    | IApp h1 h2 => exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact .IApp h1 h2

theorem fb_App_iff {M N : Trm} : fb (app M N) ↔ inert M ∧ fb N := by
  constructor
  · intro h; cases h with
    | FInert h => exact inert_App_iff.1 h
  · rintro ⟨h1, h2⟩; exact .FInert (.IApp h1 h2)

theorem fb_cases {M : Trm} (h : fb M) :
    inert M ∨ (∃ x B, M = lam x B) ∨ (∃ x B L, M = comp (lam x B) L) ∨ M = iden ∨
    (∃ N x L, M = extn N x L) ∨ (∃ x, M = nm x) := by
  cases h with
  | FInert h => exact .inl h
  | FLam => exact .inr (.inl ⟨_, _, rfl⟩)
  | FClo => exact .inr (.inr (.inl ⟨_, _, _, rfl⟩))
  | FId => exact .inr (.inr (.inr (.inl rfl)))
  | FExtn => exact .inr (.inr (.inr (.inr (.inl ⟨_, _, _, rfl⟩))))
  | FNm => exact .inr (.inr (.inr (.inr (.inr ⟨_, rfl⟩))))

theorem not_inert_Lam (x : Var) (B : Trm) : ¬ inert (lam x B) := by intro h; cases h
theorem not_inert_Clo (x : Var) (B L : Trm) : ¬ inert (comp (lam x B) L) := by
  intro h; cases h
theorem not_inert_Id : ¬ inert iden := by intro h; cases h
theorem not_inert_Extn (N : Trm) (x : Var) (L : Trm) : ¬ inert (extn N x L) := by
  intro h; cases h

/-- Isabelle's `not_inert` (four facts). -/
theorem not_inert :
    (∀ x B, ¬ inert (lam x B)) ∧ (∀ x B L, ¬ inert (comp (lam x B) L)) ∧ ¬ inert iden ∧
    (∀ N x L, ¬ inert (extn N x L)) :=
  ⟨not_inert_Lam, not_inert_Clo, not_inert_Id, not_inert_Extn⟩

theorem inert_not_Lam {M : Trm} {x : Var} {B : Trm} (h : inert M) : M ≠ lam x B := by
  rintro rfl; exact not_inert_Lam _ _ h
theorem inert_not_Clo {M : Trm} {x : Var} {B L : Trm} (h : inert M) : M ≠ comp (lam x B) L := by
  rintro rfl; exact not_inert_Clo _ _ _ h
theorem inert_not_Extn {M N : Trm} {x : Var} {L : Trm} (h : inert M) : M ≠ extn N x L := by
  rintro rfl; exact not_inert_Extn _ _ _ h
theorem inert_not_Id {M : Trm} (h : inert M) : M ≠ iden := by
  rintro rfl; exact not_inert_Id h

/-! ## β_v -/

inductive beta : Trm → Trm → Prop where
  | Beta1 {N : Trm} (x : Var) (M L : Trm) : fb N →
      beta (app (comp (lam x M) L) N) (comp M (extn N x L))
  | Beta2 {N : Trm} (x : Var) (M : Trm) : fb N →
      beta (app (lam x M) N) (comp M (extn N x iden))
  | AppL {M N : Trm} (L : Trm) : beta M N → beta (app M L) (app N L)
  | AppR {L : Trm} {M N : Trm} : fb L → beta M N → beta (app L M) (app L N)
  | VarClos (x y : Var) (M L : Trm) :
      beta (comp (var x) (comp (lam y M) L)) (comp M (extn (nm x) y L))
  | VarLam (x y : Var) (M : Trm) : beta (comp (var x) (lam y M)) (comp M (extn (nm x) y iden))
  | VarR {M N : Trm} (x : Var) : beta M N → beta (comp (var x) M) (comp (var x) N)

def cbv (M N : Trm) : Prop := Sig M N ∨ beta M N

abbrev cbv_steps : Trm → Trm → Prop := Star cbv

abbrev NF (M : Trm) : Prop := normal cbv M

theorem sig_imp_cbv {M N : Trm} (h : Sig M N) : cbv M N := Or.inl h
theorem beta_imp_cbv {M N : Trm} (h : beta M N) : cbv M N := Or.inr h

/-! ## Fireballs are closed under σ and have no β_v-redex -/

theorem sig_inert_fb (M : Trm) :
    (inert M → ∀ N, Sig M N → inert N) ∧ (fb M → ∀ N, Sig M N → fb N) := by
  induction M with
  | var x => exact ⟨fun _ N h => (nomatch h), fun _ N h => (nomatch h)⟩
  | nm x => exact ⟨fun _ N h => (nomatch h), fun _ N h => (nomatch h)⟩
  | lam x M _ =>
    refine ⟨fun h => absurd h (not_inert_Lam _ _), fun _ N h => ?_⟩
    cases h with
    | Lam _ _ => exact .FLam _ _
  | app M1 M2 ih1 ih2 =>
    have i : inert (app M1 M2) → ∀ N, Sig (app M1 M2) N → inert N := by
      intro h N hs
      obtain ⟨a1, a2⟩ := inert_App_iff.1 h
      cases hs with
      | AppConst _ x => exact .IComp x a1
      | AppL _ h => exact .IApp (ih1.1 a1 _ h) a2
      | AppR _ h => exact .IApp a1 (ih2.2 a2 _ h)
    exact ⟨i, fun h N hs => .FInert (i (inert_App_iff.2 (fb_App_iff.1 h)) N hs)⟩
  | iden => exact ⟨fun _ N h => (nomatch h), fun _ N h => (nomatch h)⟩
  | extn M1 x M2 _ _ =>
    refine ⟨fun h => absurd h (not_inert_Extn _ _ _), fun _ N h => ?_⟩
    cases h <;> exact .FExtn _ _ _
  | comp M1 M2 ih1 ih2 =>
    have i : inert (comp M1 M2) → ∀ N, Sig (comp M1 M2) N → inert N := by
      intro h N hs
      cases h with
      | IComp x m2 =>
        cases hs with
        | IdR => exact absurd rfl (inert_not_Id m2)
        | VarRef => exact absurd rfl (inert_not_Extn m2)
        | VarSkip _ _ _ => exact absurd rfl (inert_not_Extn m2)
        | CompL _ h => exact nomatch h
        | CompR _ h => exact .IComp x (ih2.1 m2 _ h)
    refine ⟨i, fun h N hs => ?_⟩
    rcases fb_cases h with h | ⟨_, _, h⟩ | ⟨x, B, L, h'⟩ | h | ⟨_, _, _, h⟩ | ⟨_, h⟩
    · exact .FInert (i h N hs)
    · cases h
    · cases h'
      cases hs with
      | IdR => exact .FLam _ _
      | CompL _ h =>
        cases h with
        | Lam _ _ => exact .FClo _ _ _
      | CompR _ h => exact .FClo _ _ _
    · cases h
    · cases h
    · cases h

theorem sig_fb {M N : Trm} (h : fb M) (hs : Sig M N) : fb N := (sig_inert_fb M).2 h N hs
theorem sig_inert {M N : Trm} (h : inert M) (hs : Sig M N) : inert N :=
  (sig_inert_fb M).1 h N hs

theorem sig_steps_fb {M N : Trm} (h : Star Sig M N) (hf : fb M) : fb N := by
  induction h with
  | refl => exact hf
  | step hs _ ih => exact ih (sig_fb hf hs)

theorem Var_no_beta {x : Var} {N : Trm} (h : beta (var x) N) : False := by cases h
theorem Nm_no_beta {x : Var} {N : Trm} (h : beta (nm x) N) : False := by cases h
theorem Id_no_beta {N : Trm} (h : beta iden N) : False := by cases h
theorem Lam_no_beta {x : Var} {M N : Trm} (h : beta (lam x M) N) : False := by cases h
theorem Extn_no_beta {M : Trm} {x : Var} {L N : Trm} (h : beta (extn M x L) N) : False := by
  cases h
theorem Clo_no_beta {x : Var} {M L N : Trm} (h : beta (comp (lam x M) L) N) : False := by
  cases h

theorem inert_fb_no_beta (M : Trm) :
    (inert M → ∀ N, ¬ beta M N) ∧ (fb M → ∀ N, ¬ beta M N) := by
  induction M with
  | var x => exact ⟨fun _ N h => (nomatch h), fun _ N h => (nomatch h)⟩
  | nm x => exact ⟨fun _ N h => (nomatch h), fun _ N h => (nomatch h)⟩
  | lam x M _ => exact ⟨fun _ N h => (nomatch h), fun _ N h => (nomatch h)⟩
  | iden => exact ⟨fun _ N h => (nomatch h), fun _ N h => (nomatch h)⟩
  | extn M x L _ _ => exact ⟨fun _ N h => (nomatch h), fun _ N h => (nomatch h)⟩
  | app M1 M2 ih1 ih2 =>
    have i : inert (app M1 M2) → ∀ N, ¬ beta (app M1 M2) N := by
      intro h N b
      obtain ⟨a1, a2⟩ := inert_App_iff.1 h
      cases b with
      | Beta1 => exact inert_not_Clo a1 rfl
      | Beta2 => exact inert_not_Lam a1 rfl
      | AppL _ b => exact ih1.1 a1 _ b
      | AppR _ b => exact ih2.2 a2 _ b
    exact ⟨i, fun h => i (inert_App_iff.2 (fb_App_iff.1 h))⟩
  | comp M1 M2 ih1 ih2 =>
    have i : inert (comp M1 M2) → ∀ N, ¬ beta (comp M1 M2) N := by
      intro h N b
      cases h with
      | IComp x m2 =>
        cases b with
        | VarClos => exact inert_not_Clo m2 rfl
        | VarLam => exact inert_not_Lam m2 rfl
        | VarR _ b => exact ih2.1 m2 _ b
    refine ⟨i, fun h N b => ?_⟩
    rcases fb_cases h with h | ⟨_, _, h⟩ | ⟨x, B, L, h'⟩ | h | ⟨_, _, _, h⟩ | ⟨_, h⟩
    · exact i h N b
    · cases h
    · cases h'; exact Clo_no_beta b
    · cases h
    · cases h
    · cases h

theorem fb_no_beta {M N : Trm} (h : fb M) : ¬ beta M N := (inert_fb_no_beta M).2 h N

/-! ## β_v is deterministic -/

theorem beta_det {M N1 N2 : Trm} (h1 : beta M N1) (h2 : beta M N2) : N1 = N2 := by
  induction h1 generalizing N2 with
  | Beta1 x M L hf =>
    cases h2 with
    | Beta1 => rfl
    | AppL _ b => exact (Clo_no_beta b).elim
    | AppR _ b => exact (fb_no_beta hf b).elim
  | Beta2 x M hf =>
    cases h2 with
    | Beta2 => rfl
    | AppL _ b => exact (Lam_no_beta b).elim
    | AppR _ b => exact (fb_no_beta hf b).elim
  | AppL L b ih =>
    cases h2 with
    | Beta1 => exact (Clo_no_beta b).elim
    | Beta2 => exact (Lam_no_beta b).elim
    | AppL _ b' => rw [ih b']
    | AppR hf _ => exact (fb_no_beta hf b).elim
  | AppR hf b ih =>
    cases h2 with
    | Beta1 _ _ _ hf' => exact (fb_no_beta hf' b).elim
    | Beta2 _ _ hf' => exact (fb_no_beta hf' b).elim
    | AppL _ b' => exact (fb_no_beta hf b').elim
    | AppR _ b' => rw [ih b']
  | VarClos x y M L =>
    cases h2 with
    | VarClos => rfl
    | VarR _ b => exact (Clo_no_beta b).elim
  | VarLam x y M =>
    cases h2 with
    | VarLam => rfl
    | VarR _ b => exact (Lam_no_beta b).elim
  | VarR x b ih =>
    cases h2 with
    | VarClos => exact (Clo_no_beta b).elim
    | VarLam => exact (Lam_no_beta b).elim
    | VarR _ b' => rw [ih b']

/-! ## Congruences for reduction sequences -/

theorem steps_lift {α β : Type} {R : α → α → Prop} {R' : β → β → Prop} {f : α → β}
    (h : ∀ P Q, R P Q → R' (f P) (f Q)) {M N : α} (hs : Star R M N) : Star R' (f M) (f N) :=
  Star.map f h hs

theorem cbv_AppL {M N : Trm} (L : Trm) (h : cbv M N) : cbv (app M L) (app N L) := by
  rcases h with h | h
  · exact Or.inl (.AppL L h)
  · exact Or.inr (.AppL L h)

theorem cbv_VarR {M N : Trm} (x : Var) (h : cbv M N) : cbv (comp (var x) M) (comp (var x) N) := by
  rcases h with h | h
  · exact Or.inl (.CompR _ h)
  · exact Or.inr (.VarR x h)

theorem cbv_steps_AppL {M M' : Trm} (N : Trm) (h : Star cbv M M') :
    Star cbv (app M N) (app M' N) :=
  steps_lift (f := fun P => app P N) (fun _ _ h => cbv_AppL N h) h

theorem cbv_steps_VarR {M M' : Trm} (x : Var) (h : Star cbv M M') :
    Star cbv (comp (var x) M) (comp (var x) M') :=
  steps_lift (f := fun P => comp (var x) P) (fun _ _ h => cbv_VarR x h) h

theorem cbv_steps_AppR {L : Trm} (hL : fb L) {M M' : Trm} (h : Star cbv M M') :
    Star cbv (app L M) (app L M') :=
  steps_lift (f := fun P => app L P) (fun _ _ h => by
    rcases h with h | h
    · exact Or.inl (.AppR L h)
    · exact Or.inr (.AppR hL h)) h

theorem sig_steps_cbv {M N : Trm} (h : Star Sig M N) : Star cbv M N :=
  steps_lift (f := fun P => P) (fun _ _ h => sig_imp_cbv h) h

theorem sig_steps_lift {f : Trm → Trm} (hf : ∀ P Q, Sig P Q → Sig (f P) (f Q)) {M N : Trm}
    (h : Star Sig M N) : Star Sig (f M) (f N) :=
  steps_lift hf h

end LambdaPEnvCBV
