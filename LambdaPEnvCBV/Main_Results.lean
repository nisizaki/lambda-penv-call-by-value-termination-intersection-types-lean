import LambdaPEnvCBV.Soundness

/-!
# Main results

Port of `Main_Results.thy`.

Typability characterizes call-by-value normalization, and equivalently call-by-value
termination: every reduction sequence is finite and ends in a clash-free normal form
(a fireball).
-/

namespace LambdaPEnvCBV

theorem main_characterization {M : Trm} : Typ M ↔ CFN M := ⟨soundness, completeness⟩

theorem main_characterization_SN {M : Trm} : Typ M ↔ CFSN M :=
  main_characterization.trans CFN_iff_CFSN

theorem Typ_imp_SN {M : Trm} (h : Typ M) : SN_at cbv M :=
  (main_characterization_SN.1 h).1

theorem clash_not_Typ {M : Trm} (n : NF M) (c : ¬ fb M) : ¬ Typ M := by
  intro ht
  obtain ⟨N, r, _, f⟩ := soundness ht
  have := normal_star n r
  subst this
  exact c f

end LambdaPEnvCBV
