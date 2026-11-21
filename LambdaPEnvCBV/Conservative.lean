import LambdaPEnvCBV.Sorted
import LambdaPEnvCBV.Main_Results

/-!
# Conservativity over call-by-value λenv on sorted terms

Port of `Conservative.thy`.
-/

namespace LambdaPEnvCBV

open Trm

theorem sig0_imp_sig {M N : Trm} (h : Sig0 M N) : Sig M N := by
  induction h with
  | Ass L M N => exact .Ass L M N
  | IdL M => exact .IdL M
  | IdR M => exact .IdR M
  | DExtn L x M N => exact .DExtn L x M N
  | VarRef x M N => exact .VarRef x M N
  | VarSkip M N h => exact .VarSkip M N h
  | DApp M1 M2 N => exact .DApp M1 M2 N
  | AppL L _ ih => exact .AppL L ih
  | AppR L _ ih => exact .AppR L ih
  | Lam x _ ih => exact .Lam x ih
  | CompL L _ ih => exact .CompL L ih
  | CompR L _ ih => exact .CompR L ih
  | ExtnL x L _ ih => exact .ExtnL x L ih
  | ExtnR L x _ ih => exact .ExtnR L x ih

theorem sig_sorted_imp_sig0 {M N : Trm} (h : Sig M N) : tm M ∨ en M → Sig0 M N := by
  induction h with
  | Ass L M N => intro _; exact .Ass L M N
  | IdL M => intro _; exact .IdL M
  | IdR M => intro _; exact .IdR M
  | DExtn L x M N => intro _; exact .DExtn L x M N
  | VarRef x M N => intro _; exact .VarRef x M N
  | VarSkip M N h => intro _; exact .VarSkip M N h
  | DApp M1 M2 N => intro _; exact .DApp M1 M2 N
  | AppConst M x => intro hs; simp [tm, en] at hs
  | ConstComp x L => intro hs; simp [tm, en] at hs
  | AppL L _ ih => intro hs; simp [tm, en] at hs; exact .AppL L (ih (.inl hs.1))
  | AppR L _ ih => intro hs; simp [tm, en] at hs; exact .AppR L (ih (.inl hs.2))
  | Lam x _ ih => intro hs; simp [tm, en] at hs; exact .Lam x (ih (.inl hs))
  | CompL L _ ih =>
    intro hs; simp only [tm, en] at hs
    rcases hs with hs | hs
    · exact .CompL L (ih (.inl hs.1))
    · exact .CompL L (ih (.inr hs.1))
  | CompR L _ ih =>
    intro hs; simp only [tm, en] at hs
    rcases hs with hs | hs
    · exact .CompR L (ih (.inr hs.2))
    · exact .CompR L (ih (.inr hs.2))
  | ExtnL x L _ ih => intro hs; simp [tm, en] at hs; exact .ExtnL x L (ih (.inl hs.1))
  | ExtnR L x _ ih => intro hs; simp [tm, en] at hs; exact .ExtnR L x (ih (.inr hs.2))

theorem sorted_sig_iff {M N : Trm} (h : tm M ∨ en M) : Sig M N ↔ Sig0 M N :=
  ⟨fun hs => sig_sorted_imp_sig0 hs h, sig0_imp_sig⟩

theorem beta0_imp_beta {M N : Trm} (h : Beta0 M N) : beta M N := by
  induction h with
  | Beta1 x M L hf => exact .Beta1 x M L hf
  | Beta2 x M hf => exact .Beta2 x M hf
  | AppL L _ ih => exact .AppL L ih
  | AppR hf _ ih => exact .AppR hf ih
  | VarR x _ ih => exact .VarR x ih

theorem beta_sorted_imp_beta0 {M N : Trm} (h : beta M N) : tm M ∨ en M → Beta0 M N := by
  induction h with
  | Beta1 x M L hf => intro _; exact .Beta1 x M L hf
  | Beta2 x M hf => intro _; exact .Beta2 x M hf
  | AppL L _ ih => intro hs; simp [tm, en] at hs; exact .AppL L (ih (.inl hs.1))
  | AppR hf _ ih => intro hs; simp [tm, en] at hs; exact .AppR hf (ih (.inl hs.2))
  | VarClos x y M L => intro hs; simp [tm, en] at hs
  | VarLam x y M => intro hs; simp [tm, en] at hs
  | VarR x _ ih =>
    intro hs; simp only [tm, en] at hs
    rcases hs with hs | hs
    · exact .VarR x (ih (.inr hs.2))
    · exact absurd hs.1 (by simp [en])

theorem sorted_beta_iff {M N : Trm} (h : tm M ∨ en M) : beta M N ↔ Beta0 M N :=
  ⟨fun hs => beta_sorted_imp_beta0 hs h, beta0_imp_beta⟩

theorem sorted_cbv_iff {M N : Trm} (h : tm M ∨ en M) : cbv M N ↔ cbv0 M N := by
  unfold cbv cbv0
  rw [sorted_sig_iff h, sorted_beta_iff h]

theorem sig0_sorted {M N : Trm} (h : Sig0 M N) : (tm M → tm N) ∧ (en M → en N) := by
  induction h with
  | Ass L M N => simp only [tm, en]; grind
  | IdL M => simp only [tm, en]; grind
  | IdR M => simp only [tm, en]; grind
  | DExtn L x M N => simp only [tm, en]; grind
  | VarRef x M N => simp only [tm, en]; grind
  | VarSkip M N _ => simp only [tm, en]; grind
  | DApp M1 M2 N => simp only [tm, en]; grind
  | AppL L _ ih => simp only [tm, en]; grind
  | AppR L _ ih => simp only [tm, en]; grind
  | Lam x _ ih => simp only [tm, en]; grind
  | CompL L _ ih => simp only [tm, en]; grind
  | CompR L _ ih => simp only [tm, en]; grind
  | ExtnL x L _ ih => simp only [tm, en]; grind
  | ExtnR L x _ ih => simp only [tm, en]; grind

theorem beta0_sorted {M N : Trm} (h : Beta0 M N) : (tm M → tm N) ∧ (en M → en N) := by
  induction h with
  | Beta1 x M L hf => simp only [tm, en]; grind
  | Beta2 x M hf => simp only [tm, en]; grind
  | AppL L _ ih => simp only [tm, en]; grind
  | AppR hf _ ih => simp only [tm, en]; grind
  | VarR x _ ih => simp only [tm, en]; grind

theorem cbv_sorted {M N : Trm} (h : cbv M N) : (tm M → tm N) ∧ (en M → en N) := by
  constructor
  · intro t
    rcases (sorted_cbv_iff (.inl t)).1 h with h0 | h0
    · exact (sig0_sorted h0).1 t
    · exact (beta0_sorted h0).1 t
  · intro t
    rcases (sorted_cbv_iff (.inr t)).1 h with h0 | h0
    · exact (sig0_sorted h0).2 t
    · exact (beta0_sorted h0).2 t

theorem cbv_steps_sorted {M N : Trm} (r : Star cbv M N) (t : tm M) : tm N := by
  induction r with
  | refl => exact t
  | step h _ ih => exact ih ((cbv_sorted h).1 t)

theorem inert_not_en {M : Trm} (h : inert M) : ¬ en M := by
  cases h <;> simp [en]

theorem NF_AppL {M N : Trm} (n : NF (app M N)) : NF M :=
  fun b hb => n _ (cbv_AppL N hb)

theorem NF_AppR {M N : Trm} (n : NF (app M N)) (f : fb M) : NF N := by
  intro b hb
  rcases hb with hb | hb
  · exact n _ (.inl (.AppR M hb))
  · exact n _ (.inr (.AppR f hb))

theorem NF_CompR_Var {x : Var} {N : Trm} (n : NF (comp (var x) N)) : NF N :=
  fun b hb => n _ (cbv_VarR x hb)

theorem sorted_NF_fb' (M : Trm) :
    (tm M → NF M → fb M) ∧ (en M → NF M → fb M) := by
  have r : ∀ {A B P : Trm}, NF (comp A B) → ¬ Sig (comp A B) P :=
    fun n hs => n _ (.inl hs)
  induction M with
  | var x => exact ⟨fun _ _ => fb_Var x, fun h => h.elim⟩
  | lam x M _ => exact ⟨fun _ _ => .FLam x M, fun h => h.elim⟩
  | iden => exact ⟨fun h => h.elim, fun _ _ => .FId⟩
  | extn M1 x M2 _ _ => exact ⟨fun h => h.elim, fun _ _ => .FExtn M1 x M2⟩
  | nm x => exact ⟨fun h => h.elim, fun h => h.elim⟩
  | app M1 M2 ih1 ih2 =>
    refine ⟨fun t n => ?_, fun h => h.elim⟩
    have f1 := ih1.1 t.1 (NF_AppL n)
    have f2 := ih2.1 t.2 (NF_AppR n f1)
    rcases fb_cases f1 with h | ⟨x, B, h⟩ | ⟨x, B, L, h⟩ | h | ⟨_, _, _, h⟩ | ⟨_, h⟩
    · exact fb_App_iff.2 ⟨h, f2⟩
    · subst h; exact absurd (beta_imp_cbv (.Beta2 x B f2)) (n _)
    · subst h; exact absurd (beta_imp_cbv (.Beta1 x B L f2)) (n _)
    · subst h; exact t.1.elim
    · subst h; exact t.1.elim
    · subst h; exact t.1.elim
  | comp M1 M2 ih1 ih2 =>
    have e : en M1 → ¬ NF (comp M1 M2) := by
      intro he n
      cases M1 with
      | var _ => exact he.elim
      | lam _ _ => exact he.elim
      | app _ _ => exact he.elim
      | nm _ => exact he.elim
      | iden => exact r n (.IdL M2)
      | extn P y Q => exact r n (.DExtn P y Q M2)
      | comp P Q => exact r n (.Ass P Q M2)
    refine ⟨fun t n => ?_, fun he n => absurd n (e he.1)⟩
    cases M1 with
    | var x =>
      have f2 := ih2.2 t.2 (NF_CompR_Var n)
      rcases fb_cases f2 with h | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | h | ⟨P, y, Q, h⟩ | ⟨_, h⟩
      · exact absurd t.2 (inert_not_en h)
      · subst h; exact t.2.elim
      · subst h; exact t.2.1.elim
      · subst h; exact absurd (r n (.IdR _)) id
      · subst h
        by_cases hy : y = x
        · subst hy; exact absurd (r n (.VarRef _ _ _)) id
        · exact absurd (r n (.VarSkip (x := y) (y := x) _ _ hy)) id
      · subst h; exact t.2.elim
    | lam x B => exact .FClo x B M2
    | app P Q => exact absurd (r n (.DApp P Q M2)) id
    | iden => exact absurd (r n (.IdL M2)) id
    | extn P y Q => exact absurd (r n (.DExtn P y Q M2)) id
    | comp P Q => exact absurd (r n (.Ass P Q M2)) id
    | nm x => exact t.1.elim

theorem sorted_NF_fb {N : Trm} (t : tm N) (n : NF N) : fb N := (sorted_NF_fb' N).1 t n

theorem sorted_cbv_steps_iff {M N : Trm} (t : tm M) : Star cbv M N ↔ Star cbv0 M N := by
  constructor
  · intro r
    induction r with
    | refl => exact .refl _
    | step h _ ih =>
      exact .step ((sorted_cbv_iff (.inl t)).1 h) (ih ((cbv_sorted h).1 t))
  · intro r
    induction r with
    | refl => exact .refl _
    | step h _ ih =>
      exact .step ((sorted_cbv_iff (.inl t)).2 h)
        (ih ((cbv_sorted ((sorted_cbv_iff (.inl t)).2 h)).1 t))

theorem sorted_NF_iff {N : Trm} (t : tm N) : NF N ↔ normal cbv0 N := by
  constructor
  · intro h b hb
    exact h b ((sorted_cbv_iff (.inl t)).2 hb)
  · intro h b hb
    exact h b ((sorted_cbv_iff (.inl t)).1 hb)

theorem conservative_CFN {M : Trm} (t : tm M) : CFN M ↔ CFN0 M := by
  constructor
  · rintro ⟨N, r, n, f⟩
    have tN := cbv_steps_sorted r t
    exact ⟨N, (sorted_cbv_steps_iff t).1 r, (sorted_NF_iff tN).1 n, f⟩
  · rintro ⟨N, r, n, f⟩
    have r' := (sorted_cbv_steps_iff t).2 r
    have tN := cbv_steps_sorted r' t
    exact ⟨N, r', (sorted_NF_iff tN).2 n, f⟩

theorem conservative_Typ {M : Trm} (t : tm M) : Typ M ↔ CFN0 M :=
  main_characterization.trans (conservative_CFN t)

end LambdaPEnvCBV
