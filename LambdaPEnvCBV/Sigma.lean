import LambdaPEnvCBV.Syntax
import LambdaPEnvCBV.ARS

/-!
# The substitution calculus σ

Port of `Sigma.thy`.  σ is the σ-reduction of λpenv_wh: the λenv rules plus `AppConst` and
`ConstComp`, with all congruences.
-/

namespace LambdaPEnvCBV

open Trm

inductive Sig : Trm → Trm → Prop where
  | Ass (L M N : Trm) : Sig (comp (comp L M) N) (comp L (comp M N))
  | IdL (M : Trm) : Sig (comp iden M) M
  | IdR (M : Trm) : Sig (comp M iden) M
  | DExtn (L : Trm) (x : Var) (M N : Trm) : Sig (comp (extn L x M) N) (extn (comp L N) x (comp M N))
  | VarRef (x : Var) (M N : Trm) : Sig (comp (var x) (extn M x N)) M
  | VarSkip {x y : Var} (M N : Trm) : x ≠ y → Sig (comp (var y) (extn M x N)) (comp (var y) N)
  | DApp (M1 M2 N : Trm) : Sig (comp (app M1 M2) N) (app (comp M1 N) (comp M2 N))
  | AppConst (M : Trm) (x : Var) : Sig (app M (nm x)) (comp (var x) M)
  | ConstComp (x : Var) (L : Trm) : Sig (comp (nm x) L) (nm x)
  | AppL {M N : Trm} (L : Trm) : Sig M N → Sig (app M L) (app N L)
  | AppR {M N : Trm} (L : Trm) : Sig M N → Sig (app L M) (app L N)
  | Lam {M N : Trm} (x : Var) : Sig M N → Sig (lam x M) (lam x N)
  | CompL {M N : Trm} (L : Trm) : Sig M N → Sig (comp M L) (comp N L)
  | CompR {M N : Trm} (L : Trm) : Sig M N → Sig (comp L M) (comp L N)
  | ExtnL {M N : Trm} (x : Var) (L : Trm) : Sig M N → Sig (extn M x L) (extn N x L)
  | ExtnR {M N : Trm} (L : Trm) (x : Var) : Sig M N → Sig (extn L x M) (extn L x N)

abbrev sig_normal (M : Trm) : Prop := normal Sig M

/-! ## σ terminates (measure `tlength`) -/

theorem sig_tlength_decrease {M N : Trm} (h : Sig M N) : tlength N < tlength M := by
  induction h with
  | Ass L M N =>
    simp only [tlength]
    have hL := tlength_pos L
    have hN := tlength_pos N
    have : tlength M * (tlength N + 1) + 1 < (tlength M + 1) * (tlength N + 1) := by
      rw [Nat.add_mul]; omega
    calc tlength L * (tlength M * (tlength N + 1) + 1)
        < tlength L * ((tlength M + 1) * (tlength N + 1)) := Nat.mul_lt_mul_of_pos_left this hL
      _ = tlength L * (tlength M + 1) * (tlength N + 1) := by rw [Nat.mul_assoc]
  | IdL M => simp only [tlength]; have := tlength_pos M; omega
  | IdR M => simp only [tlength]; have := tlength_pos M; omega
  | DExtn L x M N =>
    simp only [tlength]; have := tlength_pos N
    rw [Nat.add_mul, Nat.add_mul]; omega
  | VarRef x M N => simp only [tlength]; omega
  | VarSkip M N _ =>
    simp only [tlength]; omega
  | DApp M1 M2 N =>
    simp only [tlength]; have := tlength_pos N
    rw [Nat.add_mul, Nat.add_mul]; omega
  | AppConst M x => simp only [tlength]; omega
  | ConstComp x L => simp only [tlength]; have := tlength_pos L; omega
  | AppL L _ ih => simp only [tlength]; omega
  | AppR L _ ih => simp only [tlength]; omega
  | Lam x _ ih => simp only [tlength]; omega
  | CompL L _ ih =>
    simp only [tlength]; exact Nat.mul_lt_mul_of_pos_right ih (Nat.succ_pos _)
  | CompR L _ ih =>
    simp only [tlength]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (tlength_pos L)
  | ExtnL x L _ ih => simp only [tlength]; omega
  | ExtnR L x _ ih => simp only [tlength]; omega

theorem sig_SN_aux : ∀ n (M : Trm), tlength M < n → SN_at Sig M := by
  intro n
  induction n with
  | zero => intro M h; omega
  | succ n ih =>
    intro M h
    exact SN_at.intro fun N hN => ih N (by have := sig_tlength_decrease hN; omega)

theorem sig_SN (M : Trm) : SN_at Sig M := sig_SN_aux _ M (Nat.lt_succ_self _)

end LambdaPEnvCBV
