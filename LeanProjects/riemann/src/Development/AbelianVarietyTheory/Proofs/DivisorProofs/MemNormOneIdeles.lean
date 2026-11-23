import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrongApproximationSplitPlaceSkewHermitianUnitar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceSplitsCompletelyNotMemEmbedding
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst

noncomputable section

namespace GlobalTheory.NormOneIdele

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F E) in

def N1 (σ : E →ₐ[F] E) : Subgroup (AE F E)ˣ where
  carrier := {z | (z : AE F E) * cA σ (z : AE F E) = 1}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at *
    calc (a : AE F E) * b * (cA σ a * cA σ b) = (a * cA σ a) * (b * cA σ b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    have h1 : cA σ ((a⁻¹ : (AE F E)ˣ) : AE F E) * cA σ (a : AE F E) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    calc ((a⁻¹ : (AE F E)ˣ) : AE F E) * cA σ ((a⁻¹ : (AE F E)ˣ) : AE F E)
        = ((a⁻¹ : (AE F E)ˣ) : AE F E) * cA σ ((a⁻¹ : (AE F E)ˣ) : AE F E) * ((a : AE F E) * cA σ (a : AE F E)) := by
          rw [ha, mul_one]
      _ = (((a⁻¹ : (AE F E)ˣ) : AE F E) * a) * (cA σ ((a⁻¹ : (AE F E)ˣ) : AE F E) * cA σ (a : AE F E)) := by ring
      _ = 1 := by rw [h1, Units.inv_mul, one_mul]

theorem mem_normOneIdeles {σ : E →ₐ[F] E} {z : (AE F E)ˣ} : z ∈ N1 F E σ ↔ (z : AE F E) * cA σ (z : AE F E) = 1 := Iff.rfl

example (σ : E →ₐ[F] E) : (1 : (AE F E)ˣ) ∈ N1 F E σ := (N1 F E σ).one_mem

end GlobalTheory.NormOneIdele
