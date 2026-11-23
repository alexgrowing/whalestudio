import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in

theorem _root_.GlobalTheory.HilbFam.sum_realEmb_eq_trace : ∀ (F : Type) [Field F] [NumberField F]
    [IsTotallyReal F] (y : F),
    ∑ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, ((i y : ℝ) : ℂ) = ((Algebra.trace ℚ F y : ℚ) : ℂ) := by
  intro F _ _ _ y
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := y)
  rw [show ((Algebra.trace ℚ F y : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ F y) from rfl, h]
  refine Fintype.sum_bijective (fun i : F →+* ℝ ↦ (Complex.ofRealHom.comp i).toRatAlgHom)
    ⟨?_, ?_⟩ _ _ ?_
  · intro i j hij
    ext z
    have := congrArg (fun σ : F →ₐ[ℚ] ℂ ↦ σ z) hij
    simpa using this
  · intro σ
    have hσ := IsTotallyReal.complexEmbedding_isReal (K := F) σ.toRingHom
    refine ⟨ComplexEmbedding.IsReal.embedding hσ, ?_⟩
    ext z
    simp [ComplexEmbedding.IsReal.coe_embedding_apply]
  · intro i
    simp

end GlobalTheory.HilbFam
