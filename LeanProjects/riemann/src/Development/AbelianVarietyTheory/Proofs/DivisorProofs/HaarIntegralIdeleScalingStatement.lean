import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarIntegralIdeleScaling
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_integral_idele_scaling : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ν : @Measure (AE F E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ (r : (AE F E)ˣ) (φ : AE F E → ℂ), (Integrable (fun c => φ (r.1 * c)) ν ↔ Integrable φ ν) ∧
      ∫ c, φ (r.1 * c) ∂ν = ((absE F E r : ℝ) : ℂ)⁻¹ * ∫ c, φ c ∂ν := by
  first | exact @GlobalTheory.IdeleScaleInt.integral_mul_left_idele | exact GlobalTheory.IdeleScaleInt.integral_mul_left_idele | (intros; apply GlobalTheory.IdeleScaleInt.integral_mul_left_idele <;> assumption)
