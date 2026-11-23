import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftInvariantDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianTwistToHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolMatchIntegralScalar

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKSwapV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem le_mul_qht_pow {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : UA σ J) {x C : ℝ} (k : ℕ) (hC : 0 ≤ C)
    (hx : ∀ γ : ratU σ J, x ≤ C * (ht (γ.1 * h) : ℝ) ^ k) : x ≤ C * (qht h : ℝ) ^ k := by
  have hmono : Monotone fun t : ℝ≥0 => C * (t : ℝ) ^ k := fun s t hst =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ s.2 (NNReal.coe_le_coe.2 hst) k) hC
  have hcont : Continuous fun t : ℝ≥0 => C * (t : ℝ) ^ k := continuous_const.mul (NNReal.continuous_coe.pow k)
  have e := Monotone.map_ciInf_of_continuousAt (g := fun γ : ratU σ J => ht (γ.1 * h)) hcont.continuousAt hmono
    (OrderBot.bddBelow _)
  show x ≤ C * ((⨅ γ : ratU σ J, ht (γ.1 * h) : ℝ≥0) : ℝ) ^ k
  rw [e]
  exact le_ciInf hx

end GlobalTheory.ThKSwapV
