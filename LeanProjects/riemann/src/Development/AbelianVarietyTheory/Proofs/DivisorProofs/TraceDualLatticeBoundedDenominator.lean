import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscriminantMulTraceDualIntegral
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory

theorem exists_den_traceDual_ringOfIntegers :
    ∀ {F : Type} [Field F] [NumberField F], ∃ D : ℕ, 0 < D ∧ ∀ ξ : F,
      (∀ o : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F (ξ * o) = z) → ∃ o : 𝓞 F, (D : F) * ξ = o := by
  intro F _ _
  refine ⟨(NumberField.discr F).natAbs, Int.natAbs_pos.mpr (NumberField.discr_ne_zero F), ?_⟩
  intro ξ hξ
  have hint := GlobalTheory.discr_mul_isIntegral_of_traceDual F ξ hξ
  have hint' : IsIntegral ℤ (((NumberField.discr F).natAbs : F) * ξ) := by
    rcases Int.natAbs_eq (NumberField.discr F) with h | h
    · have : ((NumberField.discr F).natAbs : F) = (NumberField.discr F : F) := by
        have h' : ((NumberField.discr F).natAbs : ℤ) = NumberField.discr F := by omega
        rw [← Int.cast_natCast, h']
      rw [this]; exact hint
    · have : ((NumberField.discr F).natAbs : F) = -(NumberField.discr F : F) := by
        have h' : ((NumberField.discr F).natAbs : ℤ) = -(NumberField.discr F) := by omega
        rw [← Int.cast_natCast, h', Int.cast_neg]
      rw [this, neg_mul]; exact hint.neg
  exact ⟨⟨_, hint'⟩, rfl⟩

end GlobalTheory
