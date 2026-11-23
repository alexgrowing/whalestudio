import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulIsTensorPairing
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateTwist_mul_isTensorPairing : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∃ μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl (tw q k)), μ.IsTensor ∧ ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ)) = Sec.map (sglι _) (twGen k ζ) := by
  first
  | exact @GlobalTheory.EtC.TwMul.tw_mul_isTensor
  | exact GlobalTheory.EtC.TwMul.tw_mul_isTensor
  | (intros; apply GlobalTheory.EtC.TwMul.tw_mul_isTensor <;> assumption)
