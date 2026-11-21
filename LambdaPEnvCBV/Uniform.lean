import LambdaPEnvCBV.Sig_Confluence
import LambdaPEnvCBV.Reduction

/-!
# Normalization notions and uniform normalization

Port of `Uniform.thy`.

A normal form is clash-free if it is a fireball.  `CFN M`: some reduction from `M`
reaches a clash-free normal form.  `CFSN M`: every reduction from `M` terminates and
every normal form reachable from `M` is clash-free.

Adaptation: Isabelle's `SOME` in `snf` is `Classical.choose`; `M →v* N` is `Star cbv M N`.
-/

namespace LambdaPEnvCBV

open Trm

def CFN (M : Trm) : Prop := ∃ N, Star cbv M N ∧ NF N ∧ fb N

def CFSN (M : Trm) : Prop := SN_at cbv M ∧ ∀ N, Star cbv M N → NF N → fb N

theorem NF_iff {M : Trm} : NF M ↔ sig_normal M ∧ normal beta M := by
  constructor
  · intro h; exact ⟨fun N hs => h N (Or.inl hs), fun N hb => h N (Or.inr hb)⟩
  · rintro ⟨h1, h2⟩ N (h | h)
    · exact h1 N h
    · exact h2 N h

theorem fb_NF {M : Trm} (hf : fb M) (hs : sig_normal M) : NF M := by
  rintro N (h | h)
  · exact hs N h
  · exact fb_no_beta hf h

theorem NF_imp_sig_normal {M : Trm} (h : NF M) : sig_normal M := (NF_iff.1 h).1

/-! ## σ-steps commute with the β_v-step -/

theorem ss1 {M N : Trm} (h : Sig M N) : Star Sig M N := Star.single h

theorem Lam_sig_inv {x : Var} {B P : Trm} (h : Sig (lam x B) P) :
    ∃ B', P = lam x B' ∧ Sig B B' := by
  cases h with
  | Lam _ h => exact ⟨_, rfl, h⟩

theorem Clo_sig_inv {x : Var} {B K P : Trm} (h : Sig (comp (lam x B) K) P) :
    (∃ B', P = comp (lam x B') K ∧ Sig B B') ∨ (∃ K', P = comp (lam x B) K' ∧ Sig K K') ∨
    (K = iden ∧ P = lam x B) := by
  cases h with
  | IdR => exact .inr (.inr ⟨rfl, rfl⟩)
  | CompL _ h =>
    obtain ⟨B', rfl, h2⟩ := Lam_sig_inv h
    exact .inl ⟨_, rfl, h2⟩
  | CompR _ h => exact .inr (.inl ⟨_, rfl, h⟩)

/-- A σ-step never destroys the β_v-redex: the strong form below. -/
theorem beta_sig_commute {M M2 M1 : Trm} (hb : beta M M2) (hs : Sig M M1) :
    ∃ M3, beta M1 M3 ∧ Star Sig M2 M3 := by
  induction hb generalizing M1 with
  | @Beta1 N x B K hf =>
    cases hs with
    | AppL _ h =>
      rcases Clo_sig_inv h with ⟨B', rfl, h2⟩ | ⟨K', rfl, h2⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, .Beta1 _ _ _ hf, ss1 (.CompL _ h2)⟩
      · exact ⟨_, .Beta1 _ _ _ hf, ss1 (.CompR _ (.ExtnR _ _ h2))⟩
      · exact ⟨_, .Beta2 _ _ hf, .refl _⟩
    | AppR _ h =>
      exact ⟨_, .Beta1 _ _ _ (sig_fb hf h), ss1 (.CompR _ (.ExtnL _ _ h))⟩
    | AppConst _ y => exact ⟨_, .VarClos _ _ _ _, .refl _⟩
  | @Beta2 N x B hf =>
    cases hs with
    | AppL _ h =>
      obtain ⟨B', rfl, h2⟩ := Lam_sig_inv h
      exact ⟨_, .Beta2 _ _ hf, ss1 (.CompL _ h2)⟩
    | AppR _ h =>
      exact ⟨_, .Beta2 _ _ (sig_fb hf h), ss1 (.CompR _ (.ExtnL _ _ h))⟩
    | AppConst _ y => exact ⟨_, .VarLam _ _ _, .refl _⟩
  | @AppL M M' L b ih =>
    cases hs with
    | AppL _ h =>
      obtain ⟨M3, h1, h2⟩ := ih h
      exact ⟨_, .AppL _ h1, sig_steps_lift (f := fun P => app P L) (fun _ _ h => .AppL L h) h2⟩
    | AppR _ h => exact ⟨_, .AppL _ b, ss1 (.AppR _ h)⟩
    | AppConst _ y => exact ⟨_, .VarR _ b, ss1 (.AppConst _ _)⟩
  | @AppR L M M' hf b ih =>
    cases hs with
    | AppL _ h => exact ⟨_, .AppR (sig_fb hf h) b, ss1 (.AppL _ h)⟩
    | AppR _ h =>
      obtain ⟨M3, h1, h2⟩ := ih h
      exact ⟨_, .AppR hf h1, sig_steps_lift (f := fun P => app L P) (fun _ _ h => .AppR L h) h2⟩
    | AppConst _ y => exact (Nm_no_beta b).elim
  | @VarClos x y B K =>
    cases hs with
    | CompL _ h => exact nomatch h
    | CompR _ h =>
      rcases Clo_sig_inv h with ⟨B', rfl, h2⟩ | ⟨K', rfl, h2⟩ | ⟨rfl, rfl⟩
      · exact ⟨_, .VarClos _ _ _ _, ss1 (.CompL _ h2)⟩
      · exact ⟨_, .VarClos _ _ _ _, ss1 (.CompR _ (.ExtnR _ _ h2))⟩
      · exact ⟨_, .VarLam _ _ _, .refl _⟩
  | @VarLam x y B =>
    cases hs with
    | CompL _ h => exact nomatch h
    | CompR _ h =>
      obtain ⟨B', rfl, h2⟩ := Lam_sig_inv h
      exact ⟨_, .VarLam _ _ _, ss1 (.CompL _ h2)⟩
  | @VarR M M' x b ih =>
    cases hs with
    | IdR => exact (Id_no_beta b).elim
    | VarRef => exact (Extn_no_beta b).elim
    | VarSkip _ _ _ => exact (Extn_no_beta b).elim
    | CompL _ h => exact nomatch h
    | CompR _ h =>
      obtain ⟨M3, h1, h2⟩ := ih h
      exact ⟨_, .VarR _ h1,
        sig_steps_lift (f := fun P => comp (var x) P) (fun _ _ h => .CompR _ h) h2⟩

/-! ## σ-normal forms -/

theorem sig_nf (M : Trm) : ∃ N, Star Sig M N ∧ sig_normal N := by
  refine SN_at.induct (P := fun M => ∃ N, Star Sig M N ∧ sig_normal N) (sig_SN M) ?_
  intro a _ ih
  by_cases h : sig_normal a
  · exact ⟨a, .refl _, h⟩
  · have h := Classical.not_forall.1 h
    obtain ⟨b, hb⟩ := h
    replace hb := Classical.not_not.1 hb
    obtain ⟨N, h1, h2⟩ := ih b hb
    exact ⟨N, .step hb h1, h2⟩

theorem sig_steps_tlength {M N : Trm} (h : Star Sig M N) : tlength N ≤ tlength M := by
  induction h with
  | refl => exact Nat.le_refl _
  | step hs _ ih => have := sig_tlength_decrease hs; omega

/-- Isabelle's `snf M = (SOME N. sig⁺⁺* M N ∧ sig_normal N)`. -/
noncomputable def snf (M : Trm) : Trm := Classical.choose (sig_nf M)

theorem snf_spec (M : Trm) : Star Sig M (snf M) ∧ sig_normal (snf M) :=
  Classical.choose_spec (sig_nf M)

theorem snf_unique {M N : Trm} (r : Star Sig M N) (n : sig_normal N) : snf M = N := by
  obtain ⟨P, p1, p2⟩ := sig_confluent (snf_spec M).1 r
  have e1 := normal_star (snf_spec M).2 p1
  have e2 := normal_star n p2
  rw [← e1, e2]

theorem snf_steps {M M' : Trm} (r : Star Sig M M') : snf M' = snf M := by
  have h : Star Sig M (snf M') := r.trans (snf_spec M').1
  exact (snf_unique h (snf_spec M').2).symm

theorem snf_beta {M M' : Trm} (hb : beta M M') :
    ∃ M3, beta (snf M) M3 ∧ Star Sig M' M3 := by
  have key : ∀ n, ∀ M M', tlength M = n → beta M M' →
      ∃ M3, beta (snf M) M3 ∧ Star Sig M' M3 := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
      intro M M' hn hb
      by_cases h : sig_normal M
      · have : snf M = M := snf_unique (.refl _) h
        rw [this]; exact ⟨M', hb, .refl _⟩
      · have h := Classical.not_forall.1 h
        obtain ⟨M1, s⟩ := h
        replace s := Classical.not_not.1 s
        obtain ⟨M3', a1, a2⟩ := beta_sig_commute hb s
        have lt := sig_tlength_decrease s
        obtain ⟨M3, b1, b2⟩ := ih (tlength M1) (by omega) M1 M3' rfl a1
        rw [snf_steps (ss1 s)] at b1
        exact ⟨M3, b1, a2.trans b2⟩
  exact key _ M M' rfl hb

/-! ## The deterministic chain -/

inductive cd : Trm → Nat → Trm → Prop where
  | cd0 (M : Trm) : normal beta (snf M) → cd M 0 (snf M)
  | cdS {M N : Trm} {n : Nat} {E : Trm} : beta (snf M) N → cd N n E → cd M (n + 1) E

theorem cd_snf {A B : Trm} {n : Nat} {E : Trm} (h : cd A n E) (e : snf A = snf B) :
    cd B n E := by
  cases h with
  | cd0 _ hn => rw [e] at hn ⊢; exact .cd0 B hn
  | cdS hb c => exact .cdS (e ▸ hb) c

theorem cd_det {M : Trm} {n : Nat} {E : Trm} (h1 : cd M n E) :
    ∀ {n' E'}, cd M n' E' → n = n' ∧ E = E' := by
  induction h1 with
  | cd0 M hn =>
    intro n' E' h2
    cases h2 with
    | cd0 => exact ⟨rfl, rfl⟩
    | cdS hb _ => exact (hn _ hb).elim
  | cdS hb c ih =>
    intro n' E' h2
    cases h2 with
    | cd0 _ hn => exact (hn _ hb).elim
    | cdS hb' c' =>
      have := beta_det hb hb'
      subst this
      obtain ⟨e1, e2⟩ := ih c'
      exact ⟨by omega, e2⟩

theorem cd_back_sig {M M' : Trm} {n : Nat} {E : Trm} (s : Sig M M') (c : cd M' n E) :
    cd M n E := cd_snf c (snf_steps (ss1 s))

theorem cd_fwd_sig {M M' : Trm} {n : Nat} {E : Trm} (s : Sig M M') (c : cd M n E) :
    cd M' n E := cd_snf c (snf_steps (ss1 s)).symm

theorem cd_back_beta {M M' : Trm} {n : Nat} {E : Trm} (b : beta M M') (c : cd M' n E) :
    cd M (n + 1) E := by
  obtain ⟨M3, m1, m2⟩ := snf_beta b
  have : cd M3 n E := cd_snf c (snf_steps m2).symm
  exact .cdS m1 this

theorem cd_fwd_beta {M M' : Trm} {n : Nat} {E : Trm} (b : beta M M') (c : cd M n E) :
    ∃ m, n = m + 1 ∧ cd M' m E := by
  obtain ⟨M3, m1, m2⟩ := snf_beta b
  cases c with
  | cd0 _ hn => exact (hn _ m1).elim
  | cdS hb c' =>
    have := beta_det hb m1
    subst this
    exact ⟨_, rfl, cd_snf c' (snf_steps m2)⟩

theorem NF_cd {N : Trm} (n : NF N) : cd N 0 N := by
  have sn : snf N = N := snf_unique (.refl _) (NF_imp_sig_normal n)
  have hb : normal beta N := (NF_iff.1 n).2
  have hb' : normal beta (snf N) := by rw [sn]; exact hb
  have := cd.cd0 N hb'
  rwa [sn] at this

theorem steps_cd {M N : Trm} (h : Star cbv M N) (hn : NF N) : ∃ k, cd M k N := by
  induction h with
  | refl => exact ⟨0, NF_cd hn⟩
  | step hs _ ih =>
    obtain ⟨k, c⟩ := ih hn
    rcases hs with hs | hs
    · exact ⟨k, cd_back_sig hs c⟩
    · exact ⟨k + 1, cd_back_beta hs c⟩

theorem cd_SN {M : Trm} {n : Nat} {E : Trm} (h : cd M n E) : SN_at cbv M := by
  have key : ∀ n, ∀ M, cd M n E → SN_at cbv M := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n IHn =>
      have inner : ∀ t, ∀ M, tlength M = t → cd M n E → SN_at cbv M := by
        intro t
        induction t using Nat.strongRecOn with
        | _ t IHt =>
          intro M ht hc
          refine SN_at.intro fun N hs => ?_
          rcases hs with hs | hs
          · exact IHt (tlength N) (by have := sig_tlength_decrease hs; omega) N rfl
              (cd_fwd_sig hs hc)
          · obtain ⟨m, rfl, c'⟩ := cd_fwd_beta hs hc
            exact IHn m (by omega) N c'
      exact fun M hc => inner _ M rfl hc
  exact key n M h

theorem cd_reach_end {M N' : Trm} (r : Star cbv M N') :
    ∀ {n E}, cd M n E → NF N' → N' = E := by
  induction r with
  | refl =>
    intro n E c hn
    exact (cd_det (NF_cd hn) c).2
  | step hs _ ih =>
    intro n E c hn
    rcases hs with hs | hs
    · exact ih (cd_fwd_sig hs c) hn
    · obtain ⟨m, rfl, c'⟩ := cd_fwd_beta hs c
      exact ih c' hn

/-! ## Main results of this section -/

theorem NF_unique {M N1 N2 : Trm} (r1 : Star cbv M N1) (n1 : NF N1) (r2 : Star cbv M N2)
    (n2 : NF N2) : N1 = N2 := by
  obtain ⟨k, c⟩ := steps_cd r1 n1
  exact (cd_reach_end r2 c n2).symm

theorem WN_imp_SN {M N : Trm} (r : Star cbv M N) (n : NF N) : SN_at cbv M := by
  obtain ⟨k, c⟩ := steps_cd r n
  exact cd_SN c

theorem CFN_imp_CFSN {M : Trm} (h : CFN M) : CFSN M := by
  obtain ⟨N, r, n, c⟩ := h
  refine ⟨WN_imp_SN r n, fun N' r' n' => ?_⟩
  rw [← NF_unique r n r' n']; exact c

theorem SN_normalizes {M : Trm} (h : SN_at cbv M) : ∃ N, Star cbv M N ∧ NF N := by
  refine SN_at.induct (P := fun M => ∃ N, Star cbv M N ∧ NF N) h ?_
  intro a _ ih
  by_cases hn : NF a
  · exact ⟨a, .refl _, hn⟩
  · have hn := Classical.not_forall.1 hn
    obtain ⟨b, hb⟩ := hn
    replace hb := Classical.not_not.1 hb
    obtain ⟨N, h1, h2⟩ := ih b hb
    exact ⟨N, .step hb h1, h2⟩

theorem CFSN_imp_CFN {M : Trm} (h : CFSN M) : CFN M := by
  obtain ⟨sn, cf⟩ := h
  obtain ⟨N, r, n⟩ := SN_normalizes sn
  exact ⟨N, r, n, cf N r n⟩

theorem CFN_iff_CFSN {M : Trm} : CFN M ↔ CFSN M := ⟨CFN_imp_CFSN, CFSN_imp_CFN⟩

theorem CFN_back {M M' : Trm} (s : cbv M M') (h : CFN M') : CFN M := by
  obtain ⟨N, r, n, c⟩ := h
  exact ⟨N, .step s r, n, c⟩

theorem CFN_back_steps {M M' : Trm} (r : Star cbv M M') (h : CFN M') : CFN M := by
  induction r with
  | refl => exact h
  | step s _ ih => exact CFN_back s (ih h)

theorem CFN_fwd {M M' : Trm} (s : cbv M M') (c : CFN M) : CFN M' := by
  obtain ⟨sn, cf⟩ := CFN_imp_CFSN c
  have sn' : SN_at cbv M' := sn.step s
  obtain ⟨N, r, n⟩ := SN_normalizes sn'
  exact ⟨N, r, n, cf N (.step s r) n⟩

theorem CFN_fwd_steps {M M' : Trm} (r : Star cbv M M') (c : CFN M) : CFN M' := by
  induction r with
  | refl => exact c
  | step s _ ih => exact ih (CFN_fwd s c)

theorem NF_Nm (x : Var) : NF (nm x) := by
  rintro N (h | h)
  · exact nomatch h
  · exact Nm_no_beta h

theorem Nm_fwd {M M' : Trm} {x : Var} (s : cbv M M') (h : Star cbv M (nm x)) :
    Star cbv M' (nm x) := by
  have sn : SN_at cbv M := WN_imp_SN h (NF_Nm x)
  have sn' : SN_at cbv M' := sn.step s
  obtain ⟨N, r, n⟩ := SN_normalizes sn'
  have : N = nm x := NF_unique (.step s r) n h (NF_Nm x)
  subst this
  exact r

end LambdaPEnvCBV
