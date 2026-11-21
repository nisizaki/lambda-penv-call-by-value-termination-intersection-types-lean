import LambdaPEnvCBV.Main_Results

/-!
# Examples

Port of `Examples.thy`.  Variables are natural numbers: x = 0, y = 1, and so on.
Reduction is call-by-value `cbv`: the union of `Sig` and `beta`.
-/

namespace LambdaPEnvCBV

open Trm

/-! ## Helpers -/

/-- A term that reduces to a normal fireball is typable. -/
theorem ex_Typ_of_reduct {M N : Trm} (r : Star cbv M N) (n : NF N) (f : fb N) : Typ M :=
  main_characterization.mpr ⟨N, r, n, f⟩

theorem ex_no_sig_iden {N : Trm} (h : Sig iden N) : False := by cases h
theorem ex_no_sig_var {x : Var} {N : Trm} (h : Sig (var x) N) : False := by cases h
theorem ex_no_sig_nm {x : Var} {N : Trm} (h : Sig (nm x) N) : False := by cases h

theorem ex_NF_Id : NF iden :=
  fb_NF fb.FId (fun _ h => ex_no_sig_iden h)

theorem ex_NF_App_Id_Var : NF (app iden (var 1)) := by
  refine NF_iff.2 ⟨?_, ?_⟩
  · intro N h
    cases h with
    | AppL _ h' => exact ex_no_sig_iden h'
    | AppR _ h' => exact ex_no_sig_var h'
  · intro N b
    cases b with
    | AppL _ b' => exact Id_no_beta b'
    | AppR _ b' => exact Var_no_beta b'

theorem ex_NF_App_Nm_Var : NF (app (nm 0) (var 1)) := by
  refine NF_iff.2 ⟨?_, ?_⟩
  · intro N h
    cases h with
    | AppL _ h' => exact ex_no_sig_nm h'
    | AppR _ h' => exact ex_no_sig_var h'
  · intro N b
    cases b with
    | AppL _ b' => exact Nm_no_beta b'
    | AppR _ b' => exact Var_no_beta b'

theorem ex_NF_Comp_Var_Nm : NF (comp (var 0) (nm 1)) := by
  refine NF_iff.2 ⟨?_, ?_⟩
  · intro N h
    cases h with
    | CompL _ h' => exact ex_no_sig_var h'
    | CompR _ h' => exact ex_no_sig_nm h'
  · intro N b
    cases b with
    | VarR _ b' => exact Nm_no_beta b'

theorem ex_not_fb_App_Id_Var : ¬ fb (app iden (var 1)) := by
  intro h
  exact not_inert_Id (fb_App_iff.1 h).1

theorem ex_not_fb_App_Nm_Var : ¬ fb (app (nm 0) (var 1)) := by
  intro h
  cases (fb_App_iff.1 h).1

theorem ex_not_fb_Comp_Var_Nm : ¬ fb (comp (var 0) (nm 1)) := by
  intro h
  cases h with
  | FInert h' => cases h' with
    | IComp _ h'' => cases h''

/-! ## 1. `0∘(λ1.1)`, a function used as an environment -/

theorem ex1_step1 : cbv (comp (var 0) (lam 1 (var 1))) (comp (var 1) (extn (nm 0) 1 iden)) :=
  beta_imp_cbv (.VarLam 0 1 (var 1))

theorem ex1_step2 : cbv (comp (var 1) (extn (nm 0) 1 iden)) (nm 0) :=
  sig_imp_cbv (.VarRef 1 (nm 0) iden)

theorem ex1_red : Star cbv (comp (var 0) (lam 1 (var 1))) (nm 0) :=
  .step ex1_step1 (.single ex1_step2)

theorem ex1_Typ : Typ (comp (var 0) (lam 1 (var 1))) :=
  ex_Typ_of_reduct ex1_red (NF_Nm 0) (fb.FNm 0)

/-! ## 2. `(id/0·id)∘⌜0⌝`, an environment used as a function -/

theorem ex2_step1 : cbv (app (extn iden 0 iden) (nm 0)) (comp (var 0) (extn iden 0 iden)) :=
  sig_imp_cbv (.AppConst (extn iden 0 iden) 0)

theorem ex2_step2 : cbv (comp (var 0) (extn iden 0 iden)) iden :=
  sig_imp_cbv (.VarRef 0 iden iden)

theorem ex2_red : Star cbv (app (extn iden 0 iden) (nm 0)) iden :=
  .step ex2_step1 (.single ex2_step2)

theorem ex2_Typ : Typ (app (extn iden 0 iden) (nm 0)) :=
  ex_Typ_of_reduct ex2_red ex_NF_Id fb.FId

/-! ## 3. `id 1`, a clash -/

theorem ex3_not_Typ : ¬ Typ (app iden (var 1)) :=
  clash_not_Typ ex_NF_App_Id_Var ex_not_fb_App_Id_Var

/-! ## 4. `⌜0⌝ 1` and `0∘⌜1⌝`, clashes -/

theorem ex4a_not_Typ : ¬ Typ (app (nm 0) (var 1)) :=
  clash_not_Typ ex_NF_App_Nm_Var ex_not_fb_App_Nm_Var

theorem ex4b_not_Typ : ¬ Typ (comp (var 0) (nm 1)) :=
  clash_not_Typ ex_NF_Comp_Var_Nm ex_not_fb_Comp_Var_Nm

/-! ## 5. `id((λ2.⌜0⌝) 1)`, using AppR and Beta2 -/

theorem ex5_step1 :
    cbv (app iden (app (lam 2 (nm 0)) (var 1))) (app iden (comp (nm 0) (extn (var 1) 2 iden))) :=
  beta_imp_cbv (.AppR fb.FId (.Beta2 2 (nm 0) (fb_Var 1)))

theorem ex5_step2 :
    cbv (app iden (comp (nm 0) (extn (var 1) 2 iden))) (app iden (nm 0)) :=
  sig_imp_cbv (.AppR iden (.ConstComp 0 (extn (var 1) 2 iden)))

theorem ex5_step3 : cbv (app iden (nm 0)) (comp (var 0) iden) :=
  sig_imp_cbv (.AppConst iden 0)

theorem ex5_step4 : cbv (comp (var 0) iden) (var 0) :=
  sig_imp_cbv (.IdR (var 0))

theorem ex5_red : Star cbv (app iden (app (lam 2 (nm 0)) (var 1))) (var 0) :=
  .step ex5_step1 (.step ex5_step2 (.step ex5_step3 (.single ex5_step4)))

theorem ex5_Typ : Typ (app iden (app (lam 2 (nm 0)) (var 1))) :=
  ex_Typ_of_reduct ex5_red (NF_Var 0) (fb_Var 0)

end LambdaPEnvCBV
