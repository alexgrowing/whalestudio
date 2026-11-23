import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianTwistToHermitian
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_hermitian_twist_to_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B : Base F E) (n : ℕ) (W : Spc F E n) (r s : ℕ), W.IsSkew σ B r s → ∃ c₀ : E, c₀ ≠ 0 ∧ IsHermND σ (c₀ • W.J.map σ) := by
  first | exact @GlobalTheory.SkewToHerm.skew_to_hermND | exact GlobalTheory.SkewToHerm.skew_to_hermND | (intros; apply GlobalTheory.SkewToHerm.skew_to_hermND <;> assumption)
