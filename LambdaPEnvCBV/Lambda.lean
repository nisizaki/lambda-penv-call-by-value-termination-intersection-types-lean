import LambdaPEnvCBV.ARS

/-!
# Pure λ-calculus (de Bruijn) and open call-by-value

Port of `Lambda.thy`.

Definitions of `lift` and `subst` follow the Isabelle distribution
(`HOL/Proofs/Lambda/Lambda.thy`), with constructors renamed.

Adaptation: the Isabelle notation `t[s/k]` is the function `subst t s k`;
`rtranclp vred` is `Star vred`.
-/

namespace LambdaPEnvCBV

inductive dB where
  | DVar : Nat → dB
  | DApp : dB → dB → dB
  | DAbs : dB → dB
  deriving DecidableEq

open dB

def lift : dB → Nat → dB
  | DVar i, k => if i < k then DVar i else DVar (i + 1)
  | DApp s t, k => DApp (lift s k) (lift t k)
  | DAbs s, k => DAbs (lift s (k + 1))

/-- `subst t s k` is Isabelle's `t[s/k]`. -/
def subst : dB → dB → Nat → dB
  | DVar i, s, k => if k < i then DVar (i - 1) else if i = k then s else DVar i
  | DApp t u, s, k => DApp (subst t s k) (subst u s k)
  | DAbs t, s, k => DAbs (subst t (lift s 0) (k + 1))

theorem subst_Var (i : Nat) (s : dB) (k : Nat) :
    subst (DVar i) s k = (if k < i then DVar (i - 1) else if i = k then s else DVar i) := rfl

theorem subst_App (t u s : dB) (k : Nat) :
    subst (DApp t u) s k = DApp (subst t s k) (subst u s k) := rfl

theorem subst_Abs (t s : dB) (k : Nat) :
    subst (DAbs t) s k = DAbs (subst t (lift s 0) (k + 1)) := rfl

@[simp] theorem lift_Var (i k : Nat) :
    lift (DVar i) k = (if i < k then DVar i else DVar (i + 1)) := rfl
@[simp] theorem lift_App (s t : dB) (k : Nat) :
    lift (DApp s t) k = DApp (lift s k) (lift t k) := rfl
@[simp] theorem lift_Abs (s : dB) (k : Nat) :
    lift (DAbs s) k = DAbs (lift s (k + 1)) := rfl
attribute [simp] subst_App subst_Abs

@[simp] theorem subst_eq (k : Nat) (u : dB) : subst (DVar k) u k = u := by
  simp [subst_Var]

@[simp] theorem subst_gt {i j : Nat} (u : dB) (h : i < j) :
    subst (DVar j) u i = DVar (j - 1) := by
  simp [subst_Var, h]

@[simp] theorem subst_lt {i j : Nat} (u : dB) (h : j < i) :
    subst (DVar j) u i = DVar j := by
  have : j ≠ i := by omega
  simp [subst_Var, this, Nat.not_lt_of_gt h]

theorem lift_lift (t : dB) : ∀ {i k : Nat}, i < k + 1 →
    lift (lift t i) (k + 1) = lift (lift t k) i := by
  induction t with
  | DVar j =>
    intro i k h
    simp only [lift_Var]
    (repeat' split) <;> simp_all [lift_Var] <;> (repeat' split) <;> (try simp_all) <;> omega
  | DApp s t ihs iht => intro i k h; simp [ihs h, iht h]
  | DAbs s ih => intro i k h; simp [ih (by omega : i + 1 < k + 1 + 1)]

theorem lift_subst_lt (t : dB) : ∀ {i j : Nat} {s : dB}, i < j + 1 →
    lift (subst t s j) i = subst (lift t i) (lift s i) (j + 1) := by
  induction t with
  | DVar x =>
    intro i j s h
    simp only [subst_Var, lift_Var]
    (repeat' split) <;> simp_all [subst_Var, lift_Var] <;> (repeat' split) <;> (try simp_all) <;> omega
  | DApp a b iha ihb => intro i j s h; simp [iha h, ihb h]
  | DAbs a ih =>
    intro i j s h
    simp [ih (by omega : i + 1 < j + 1 + 1), lift_lift s (by omega : 0 < i + 1)]

@[simp] theorem subst_lift (t : dB) : ∀ {k : Nat} {s : dB}, subst (lift t k) s k = t := by
  induction t with
  | DVar i =>
    intro k s
    simp only [lift_Var]
    (repeat' split) <;> simp_all [subst_Var] <;> omega
  | DApp a b iha ihb => intro k s; simp [iha, ihb]
  | DAbs a ih => intro k s; simp [ih]

/-! ### Open call-by-value (the fireball calculus), left-to-right

Fireballs are abstractions and inert terms (variables applied to fireballs).
`β_f` fires when the argument is a fireball; evaluation is weak and left-to-right.
On closed terms fireballs are exactly the values, and this is Plotkin's
left-to-right call-by-value evaluation. -/

mutual
inductive dinert : dB → Prop where
  | inertVar (i : Nat) : dinert (DVar i)
  | inertApp {s t : dB} : dinert s → dfb t → dinert (DApp s t)
inductive dfb : dB → Prop where
  | fbInert {s : dB} : dinert s → dfb s
  | fbAbs (s : dB) : dfb (DAbs s)
end

inductive vred : dB → dB → Prop where
  | vbeta {t : dB} (s : dB) : dfb t → vred (DApp (DAbs s) t) (subst s t 0)
  | vappL {s s' : dB} (t : dB) : vred s s' → vred (DApp s t) (DApp s' t)
  | vappR {s t t' : dB} : dfb s → vred t t' → vred (DApp s t) (DApp s t')

@[simp] theorem dinert_not_DAbs (s : dB) : ¬ dinert (DAbs s) := by
  intro h; cases h

theorem dinert_DApp_iff {s t : dB} : dinert (DApp s t) ↔ dinert s ∧ dfb t :=
  ⟨fun h => by cases h with | inertApp a b => exact ⟨a, b⟩,
   fun ⟨a, b⟩ => .inertApp a b⟩

theorem dfb_DApp_iff {s t : dB} : dfb (DApp s t) ↔ dinert s ∧ dfb t :=
  ⟨fun h => by cases h with | fbInert h => exact dinert_DApp_iff.1 h,
   fun ⟨a, b⟩ => .fbInert (.inertApp a b)⟩

theorem dfb_normal (s : dB) : (dinert s → normal vred s) ∧ (dfb s → normal vred s) := by
  induction s with
  | DVar i =>
    have : normal vred (DVar i) := fun b h => by cases h
    exact ⟨fun _ => this, fun _ => this⟩
  | DApp s t ihs iht =>
    have key : dinert s → dfb t → normal vred (DApp s t) := by
      intro hs ht u hu
      cases hu with
      | vbeta => exact dinert_not_DAbs _ hs
      | vappL _ h => exact (ihs.1 hs) _ h
      | vappR _ h => exact (iht.2 ht) _ h
    exact ⟨fun h => key (dinert_DApp_iff.1 h).1 (dinert_DApp_iff.1 h).2,
           fun h => key (dfb_DApp_iff.1 h).1 (dfb_DApp_iff.1 h).2⟩
  | DAbs s _ =>
    have : normal vred (DAbs s) := fun b h => by cases h
    exact ⟨fun h => (dinert_not_DAbs _ h).elim, fun _ => this⟩

theorem dfb_no_vred {s t : dB} (h : dfb s) : ¬ vred s t := fun hr => (dfb_normal s).2 h t hr

theorem vred_det {s t u : dB} (h : vred s t) : vred s u → t = u := by
  induction h generalizing u with
  | vbeta s hf =>
    intro h2
    cases h2 with
    | vbeta => rfl
    | vappL _ h => cases h
    | vappR _ h => exact (dfb_no_vred hf h).elim
  | vappL t h ih =>
    intro h2
    cases h2 with
    | vbeta _ => cases h
    | vappL _ h' => rw [ih h']
    | vappR hf _ => exact (dfb_no_vred hf h).elim
  | vappR hf h ih =>
    intro h2
    cases h2 with
    | vbeta _ => exact (dfb_no_vred ‹dfb _› h).elim
    | vappL _ h' => exact (dfb_no_vred hf h').elim
    | vappR _ h' => rw [ih h']

def lam_VN (t : dB) : Prop := ∃ u, Star vred t u ∧ normal vred u

inductive vdist : dB → Nat → Prop where
  | vd0 {t : dB} : normal vred t → vdist t 0
  | vdS {t u : dB} {n : Nat} : vred t u → vdist u n → vdist t (n + 1)

theorem lam_VN_vdist {t : dB} (h : lam_VN t) : ∃ n, vdist t n := by
  obtain ⟨u, r, nf⟩ := h
  induction r with
  | refl => exact ⟨0, .vd0 nf⟩
  | step h _ ih => obtain ⟨n, hn⟩ := ih nf; exact ⟨n + 1, .vdS h hn⟩

theorem vdist_step {t u : dB} {n : Nat} (h : vdist t n) (hr : vred t u) :
    ∃ m, n = m + 1 ∧ vdist u m := by
  cases h with
  | vd0 hn => exact absurd hr (hn _)
  | vdS h' hd => rw [vred_det hr h']; exact ⟨_, rfl, hd⟩

end LambdaPEnvCBV
