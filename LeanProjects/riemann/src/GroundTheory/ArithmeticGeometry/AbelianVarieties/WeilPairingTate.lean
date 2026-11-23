import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilPairing
import GroundTheory.ArithmeticGeometry.AbelianVarieties.WeilGaloisFunctionField
import GroundTheory.ArithmeticGeometry.AbelianVarieties.TateDeterminant
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.Abelian

open WeierstrassCurve

universe u

section Tate

variable {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] {W : WeierstrassCurve F}
  [W.IsElliptic]

theorem weilPairing_nsmul_right {n : ℕ} (hn : (n : F) ≠ 0) {S T : W.toAffine.Point}
    (hS : n • S = 0) (hT : n • T = 0) (m : ℕ) :
    weilPairing W n S (m • T) = weilPairing W n S T ^ m := by
  induction m with
  | zero =>
    rw [zero_smul, pow_zero]
    have h := weilPairing_add_right hn hS (smul_zero n) (smul_zero n)
    rw [add_zero] at h
    exact mul_left_cancel₀ (weilPairing_ne_zero hn hS (smul_zero n)) (h.symm.trans (mul_one _).symm)
  | succ m ih =>
    have hmT : n • (m • T) = 0 := by rw [smul_comm, hT, smul_zero]
    rw [succ_nsmul, weilPairing_add_right hn hS hmT hT, ih, pow_succ]

end Tate

section Galois

variable {K L : Type u} [Field K] [Field L] [Algebra K L] [DecidableEq L] [IsAlgClosed L]
  (W₀ : WeierstrassCurve K) [W₀.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]

end Galois

end GroundTheory.Arith.Abelian
