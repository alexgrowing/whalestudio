import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitCokernelCoforkBiprodMap
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory
theorem ses_precomp_iso_postcomp_coker_zero : ∀ (X : Scheme.{0}) {A E₁ E₂ E₃ F : X.Modules} (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (h : a ≫ b = 0),
    (ShortComplex.mk a b h).ShortExact → ∀ (f : A ⟶ E₂) (e : A ⟶ E₁) [IsIso e], f = e ≫ a →
    ∀ (ι : F ⟶ E₃), IsZero F → ∃ hz : f ≫ b ≫ cokernel.π ι = 0,
      (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact := by
  intro X A E₁ E₂ E₃ F a b h hS f e _ hf ι hF
  have hι : ι = 0 := hF.eq_of_src _ _
  subst hι
  have hz : f ≫ b ≫ cokernel.π (0 : F ⟶ E₃) = 0 := by
    rw [hf, Category.assoc, reassoc_of% h, zero_comp, comp_zero]
  refine ⟨hz, ?_⟩
  refine ShortComplex.shortExact_of_iso ?_ hS
  refine ShortComplex.isoMk (asIso e).symm (Iso.refl _) (asIso (cokernel.π (0 : F ⟶ E₃))) ?_ ?_
  · simp [hf]
  · simp
end GlobalTheory
