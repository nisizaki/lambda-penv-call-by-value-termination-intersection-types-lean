import LambdaPEnvCBV.Conservative
import LambdaPEnvCBV.Lambda

/-!
# Readback into the λ-calculus: conservativity over open call-by-value

Port of `Readback.thy`.  `tm`, `en`, `pure` are in `Sorted`; preservation of sortedness and
`sorted_NF_fb` are in `Conservative`.
-/

namespace LambdaPEnvCBV

open Trm dB

/-- Function update. -/
def fupd {α : Type} (f : Var → α) (x : Var) (v : α) : Var → α :=
  fun y => if y = x then v else f y

/-- `junk` is used for ill-sorted positions; it is closed, so substitution fixes it. -/
def junk : dB := DAbs (DVar 0)

@[simp] theorem subst_junk (s : dB) (k : Nat) : subst junk s k = junk := by
  simp [junk, subst_Abs]

mutual
def rb : Trm → (Var → dB) → dB
  | var x, ρ => ρ x
  | lam x M, ρ => DAbs (rb M (fupd (fun y => lift (ρ y) 0) x (DVar 0)))
  | app M N, ρ => DApp (rb M ρ) (rb N ρ)
  | comp M L, ρ => rb M (rbe L ρ)
  | iden, _ => junk
  | extn _ _ _, _ => junk
  | nm _, _ => junk
def rbe : Trm → (Var → dB) → (Var → dB)
  | var _, ρ => ρ
  | lam _ _, ρ => ρ
  | app _ _, ρ => ρ
  | comp L1 L2, ρ => rbe L1 (rbe L2 ρ)
  | iden, ρ => ρ
  | extn M x L, ρ => fupd (rbe L ρ) x (rb M ρ)
  | nm _, ρ => ρ
end

theorem rb_subst (M : Trm) :
    (∀ σ s k, subst (rb M σ) s k = rb M (fun y => subst (σ y) s k)) ∧
    (∀ σ s k, rbe M (fun y => subst (σ y) s k) = (fun y => subst (rbe M σ y) s k)) := by
  induction M with
  | var x => simp [rb, rbe]
  | lam x M ih =>
    refine ⟨fun σ s k => ?_, by simp [rbe]⟩
    have fe : (fun y => subst (fupd (fun y => lift (σ y) 0) x (DVar 0) y) (lift s 0) (k + 1))
        = fupd (fun y => lift (subst (σ y) s k) 0) x (DVar 0) := by
      funext y
      by_cases h : y = x
      · simp [fupd, h]
      · simp [fupd, h, lift_subst_lt]
    simp only [rb, subst_Abs]
    rw [ih.1, fe]
  | app M N ihM ihN =>
    exact ⟨fun σ s k => by simp [rb, ihM.1, ihN.1], by simp [rbe]⟩
  | iden => exact ⟨by simp [rb], by simp [rbe]⟩
  | nm x => exact ⟨by simp [rb], by simp [rbe]⟩
  | extn M x L ihM ihL =>
    refine ⟨by simp [rb], fun σ s k => ?_⟩
    simp only [rbe]
    funext y
    rw [ihL.2, ← ihM.1 σ s k]
    by_cases h : y = x <;> simp [fupd, h]
  | comp M L ihM ihL =>
    refine ⟨fun σ s k => ?_, fun σ s k => ?_⟩
    · simp only [rb]; rw [ihM.1, ihL.2]
    · simp only [rbe]; rw [ihL.2, ihM.2]

theorem beta_rb (M : Trm) (σ : Var → dB) (x : Var) (t : dB) :
    subst (rb M (fupd (fun y => lift (σ y) 0) x (DVar 0))) t 0 = rb M (fupd σ x t) := by
  have : (fun y => subst (fupd (fun y => lift (σ y) 0) x (DVar 0) y) t 0) = fupd σ x t := by
    funext y
    by_cases h : y = x <;> simp [fupd, h]
  rw [(rb_subst M).1, this]

/-! ## Simulation -/

theorem sig_sorted {M N : Trm} (h : Sig0 M N) :
    (tm M → tm N ∧ ∀ ρ, rb N ρ = rb M ρ) ∧ (en M → en N ∧ ∀ ρ, rbe N ρ = rbe M ρ) := by
  induction h with
  | Ass L M N => simp [tm, en, rb, rbe, and_assoc]
  | IdL M => simp [tm, en, rb, rbe]
  | IdR M => simp [tm, en, rb, rbe]
  | DExtn L x M N => simp [tm, en, rb, rbe, and_assoc, and_comm, and_left_comm]
  | VarRef x M N => simp +contextual [tm, en, rb, rbe, fupd]
  | VarSkip M N hxy =>
    rename_i x y
    refine ⟨?_, ?_⟩ <;> simp [tm, en, rb, rbe, fupd, Ne.symm hxy]
  | DApp M1 M2 N => simp [tm, en, rb, rbe, and_assoc, and_comm, and_left_comm]
  | AppL L _ ih =>
    refine ⟨fun ⟨a, b⟩ => ⟨⟨(ih.1 a).1, b⟩, fun ρ => ?_⟩, by simp [en]⟩
    simp [rb, (ih.1 a).2]
  | AppR L _ ih =>
    refine ⟨fun ⟨a, b⟩ => ⟨⟨a, (ih.1 b).1⟩, fun ρ => ?_⟩, by simp [en]⟩
    simp [rb, (ih.1 b).2]
  | Lam x _ ih =>
    refine ⟨fun a => ⟨(ih.1 a).1, fun ρ => ?_⟩, by simp [en]⟩
    simp [rb, (ih.1 a).2]
  | CompL L _ ih =>
    refine ⟨fun ⟨a, b⟩ => ⟨⟨(ih.1 a).1, b⟩, fun ρ => ?_⟩, fun ⟨a, b⟩ => ⟨⟨(ih.2 a).1, b⟩, fun ρ => ?_⟩⟩
    · simp [rb, (ih.1 a).2]
    · simp [rbe, (ih.2 a).2]
  | CompR L _ ih =>
    refine ⟨fun ⟨a, b⟩ => ⟨⟨a, (ih.2 b).1⟩, fun ρ => ?_⟩, fun ⟨a, b⟩ => ⟨⟨a, (ih.2 b).1⟩, fun ρ => ?_⟩⟩
    · simp [rb, (ih.2 b).2]
    · simp [rbe, (ih.2 b).2]
  | ExtnL x L _ ih =>
    refine ⟨by simp [tm], fun ⟨a, b⟩ => ⟨⟨(ih.1 a).1, b⟩, fun ρ => ?_⟩⟩
    simp [rbe, (ih.1 a).2]
  | ExtnR L x _ ih =>
    refine ⟨by simp [tm], fun ⟨a, b⟩ => ⟨⟨a, (ih.2 b).1⟩, fun ρ => ?_⟩⟩
    simp [rbe, (ih.2 b).2]

theorem beta_not_en {M N : Trm} (h : Beta0 M N) : ¬ en M := by
  induction h <;> simp_all [en]

theorem fb_rb (M : Trm) (t : tm M) :
    (inert M → dinert (rb M DVar)) ∧ (fb M → dfb (rb M DVar)) := by
  induction M with
  | var x => exact ⟨fun _ => .inertVar x, fun _ => .fbInert (.inertVar x)⟩
  | lam x M _ => exact ⟨fun h => absurd h (not_inert_Lam _ _), fun _ => .fbAbs _⟩
  | app M1 M2 ih1 ih2 =>
    have i : inert (app M1 M2) → dinert (rb (app M1 M2) DVar) := by
      intro h
      obtain ⟨a, b⟩ := inert_App_iff.1 h
      exact .inertApp ((ih1 t.1).1 a) ((ih2 t.2).2 b)
    exact ⟨i, fun h => .fbInert (i (inert_App_iff.2 (fb_App_iff.1 h)))⟩
  | iden => exact t.elim
  | extn => exact t.elim
  | nm => exact t.elim
  | comp M1 M2 ih1 ih2 =>
    have i : ¬ inert (comp M1 M2) := by
      intro h
      cases h with
      | IComp x h2 => exact inert_not_en h2 t.2
    refine ⟨fun h => absurd h i, fun h => ?_⟩
    rcases fb_cases h with h | ⟨_, _, h⟩ | ⟨x, B, L, h⟩ | h | ⟨_, _, _, h⟩ | ⟨_, h⟩
    · exact absurd h i
    · cases h
    · cases h; exact .fbAbs _
    · cases h
    · cases h
    · cases h

theorem beta_sorted {M N : Trm} (h : Beta0 M N) :
    tm M → tm N ∧ vred (rb M DVar) (rb N DVar) := by
  induction h with
  | Beta1 x M L hf =>
    rename_i N
    intro ⟨⟨a, b⟩, c⟩
    refine ⟨⟨a, c, b⟩, ?_⟩
    have f : dfb (rb N DVar) := (fb_rb N c).2 hf
    have := vred.vbeta (rb M (fupd (fun y => lift (rbe L DVar y) 0) x (DVar 0))) f
    rw [beta_rb] at this
    simpa [rb, rbe] using this
  | Beta2 x M hf =>
    rename_i N
    intro ⟨a, b⟩
    refine ⟨⟨a, b, trivial⟩, ?_⟩
    have f : dfb (rb N DVar) := (fb_rb N b).2 hf
    have := vred.vbeta (rb M (fupd (fun y => lift (DVar y) 0) x (DVar 0))) f
    rw [beta_rb] at this
    simpa [rb, rbe] using this
  | AppL L _ ih =>
    intro ⟨a, b⟩
    obtain ⟨c, d⟩ := ih a
    exact ⟨⟨c, b⟩, vred.vappL _ d⟩
  | @AppR L M N hf _ ih =>
    intro ⟨a, b⟩
    obtain ⟨c, d⟩ := ih b
    exact ⟨⟨a, c⟩, vred.vappR ((fb_rb L a).2 hf) d⟩
  | VarR x h _ =>
    intro ⟨_, b⟩
    exact absurd b (beta_not_en h)

theorem rb_cbv_sorted {M N : Trm} (h : cbv M N) (t : tm M) :
    tm N ∧ ((rb N DVar = rb M DVar ∧ tlength N < tlength M) ∨ vred (rb M DVar) (rb N DVar)) := by
  rcases h with h | h
  · have h0 := (sorted_sig_iff (.inl t)).1 h
    exact ⟨((sig_sorted h0).1 t).1, Or.inl ⟨((sig_sorted h0).1 t).2 DVar, sig_tlength_decrease h⟩⟩
  · have h0 := (sorted_beta_iff (.inl t)).1 h
    exact ⟨(beta_sorted h0 t).1, Or.inr (beta_sorted h0 t).2⟩

theorem rb_cbv_steps_sorted {M N : Trm} (h : Star cbv M N) (t : tm M) :
    tm N ∧ Star vred (rb M DVar) (rb N DVar) := by
  induction h with
  | refl => exact ⟨t, .refl _⟩
  | @step a b c hab _ ih =>
    obtain ⟨t1, h1⟩ := rb_cbv_sorted hab t
    obtain ⟨t2, h2⟩ := ih t1
    refine ⟨t2, ?_⟩
    rcases h1 with ⟨e, _⟩ | e
    · rw [e] at h2; exact h2
    · exact .step e h2

/-! ## Conservativity -/

theorem CFN_imp_lam_VN {M : Trm} (t : tm M) (c : CFN M) : lam_VN (rb M DVar) := by
  obtain ⟨N, r, _, f⟩ := c
  obtain ⟨tN, h⟩ := rb_cbv_steps_sorted r t
  have : dfb (rb N DVar) := (fb_rb N tN).2 f
  exact ⟨_, h, (dfb_normal _).2 this⟩

theorem vdist_imp_SN {M : Trm} {n : Nat} (h : vdist (rb M DVar) n) (t : tm M) : SN_at cbv M := by
  induction n using Nat.strongRecOn generalizing M with
  | _ n IHn =>
    have key : ∀ k (M : Trm), tlength M ≤ k → vdist (rb M DVar) n → tm M → SN_at cbv M := by
      intro k
      induction k with
      | zero => intro M hk; have := tlength_pos M; omega
      | succ k ihk =>
        intro M hk hd tM
        refine SN_at.intro fun N s => ?_
        obtain ⟨tN, c⟩ := rb_cbv_sorted s tM
        rcases c with ⟨e, lt⟩ | e
        · exact ihk N (by omega) (by rw [e]; exact hd) tN
        · obtain ⟨m, hm, hd'⟩ := vdist_step hd e
          exact IHn m (by omega) hd' tN
    exact key _ M (Nat.le_refl _) h t

theorem lam_VN_imp_CFSN {M : Trm} (t : tm M) (w : lam_VN (rb M DVar)) : CFSN M := by
  obtain ⟨n, hn⟩ := lam_VN_vdist w
  exact ⟨vdist_imp_SN hn t, fun N r n => sorted_NF_fb (cbv_steps_sorted r t) n⟩

theorem conservativity_sorted {M : Trm} (t : tm M) :
    (lam_VN (rb M DVar) ↔ CFN M) ∧ (CFN M ↔ CFSN M) ∧ (Typ M ↔ CFN M) :=
  ⟨⟨fun w => CFSN_imp_CFN (lam_VN_imp_CFSN t w), CFN_imp_lam_VN t⟩,
   CFN_iff_CFSN, main_characterization⟩

theorem conservativity {M : Trm} (h : pure M) :
    (Typ M ↔ lam_VN (rb M DVar)) ∧ (lam_VN (rb M DVar) ↔ CFSN M) := by
  have c := conservativity_sorted (pure_tm h)
  exact ⟨c.2.2.trans c.1.symm, c.1.trans CFN_iff_CFSN⟩

end LambdaPEnvCBV
