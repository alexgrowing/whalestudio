import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_exponent_of_infinityType : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (χ : HChar E), (∀ n : (E →+* ℂ) → ℤ, χ.IsAlg n → ∀ τ, expo χ τ = n τ) ∧ (∀ s : ℝ, χ.IsAbsPow s → ∀ τ, expo χ τ = s) ∧ ∀ (I : Type) [Fintype I] (φ : I → E →+* ℂ) (n : I → ℤ), Function.Injective (fun i => InfinitePlace.mk (φ i)) → χ.HasInf φ n → ∀ i, expo χ (φ i) = (n i : ℂ) / 2 ∧ expo χ (ComplexEmbedding.conjugate (φ i)) = -(n i : ℂ) / 2 := by
  first | exact @GlobalTheory.CuspRep.InfType.expo_of_infType | exact GlobalTheory.CuspRep.InfType.expo_of_infType | (intros; apply GlobalTheory.CuspRep.InfType.expo_of_infType <;> assumption)
