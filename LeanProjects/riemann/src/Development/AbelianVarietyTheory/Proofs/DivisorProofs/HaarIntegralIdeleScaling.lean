import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarScalingMultiplicative
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

namespace GlobalTheory.IdeleScaleInt

theorem integral_mul_left_idele : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ ν : @Measure (AE F E) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ (r : (AE F E)ˣ) (φ : AE F E → ℂ), (Integrable (fun c => φ (r.1 * c)) ν ↔ Integrable φ ν) ∧
      ∫ c, φ (r.1 * c) ∂ν = ((absE F E r : ℝ) : ℂ)⁻¹ * ∫ c, φ c ∂ν := by
  intro F E _ _ _ _ _ σ hσ ν hν r φ
  letI : MeasurableSpace (AE F E) := borel _
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have hmap := GlobalTheory.AdeleUnitModule.map_mul_eq_absE_inv_smul F E σ hσ ν hν r
  let h : AE F E ≃ₜ AE F E :=
    { toFun := fun x => (r : AE F E) * x
      invFun := fun x => ((r⁻¹ : (AE F E)ˣ) : AE F E) * x
      left_inv := fun x => by simp [← mul_assoc]
      right_inv := fun x => by simp [← mul_assoc]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  have he : MeasurableEmbedding (fun x : AE F E => (r : AE F E) * x) := h.measurableEmbedding
  have hone : absE F E r * absE F E r⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hne : absE F E r ≠ 0 := left_ne_zero_of_mul_eq_one hone
  have hpos : (0 : ℝ≥0) < absE F E r := pos_iff_ne_zero.mpr hne
  have hc0 : ((absE F E r : ENNReal))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr ENNReal.coe_ne_top
  have hct : ((absE F E r : ENNReal))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by exact_mod_cast hpos.ne')
  constructor
  · change Integrable (φ ∘ fun x => (r : AE F E) * x) ν ↔ _
    rw [← he.integrable_map_iff, hmap, integrable_smul_measure hc0 hct]
  · have h1 : ∫ c, φ ((r : AE F E) * c) ∂ν = ∫ c, φ c ∂(ν.map fun x => (r : AE F E) * x) :=
      (he.integral_map φ).symm
    rw [h1, hmap, integral_smul_measure, ENNReal.toReal_inv, ENNReal.coe_toReal, Complex.real_smul]
    push_cast
    rfl

end GlobalTheory.IdeleScaleInt
