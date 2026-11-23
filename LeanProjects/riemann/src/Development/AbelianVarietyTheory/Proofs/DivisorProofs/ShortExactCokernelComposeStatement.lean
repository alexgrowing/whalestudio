import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactCokernelCompose
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitCokernelCoforkBiprodMap
open CategoryTheory Limits AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.short_exact_cokernel_compose : ∀ (X : Scheme.{0}) {A E₁ E₂ E₃ F : X.Modules} (a : E₁ ⟶ E₂) (b : E₂ ⟶ E₃) (h : a ≫ b = 0),
    (ShortComplex.mk a b h).ShortExact → ∀ (f : A ⟶ E₂) (e : A ⟶ E₁) [IsIso e], f = e ≫ a →
    ∀ (ι : F ⟶ E₃), IsZero F → ∃ hz : f ≫ b ≫ cokernel.π ι = 0,
      (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact := by
  first | exact @GlobalTheory.ses_precomp_iso_postcomp_coker_zero | exact GlobalTheory.ses_precomp_iso_postcomp_coker_zero | (intros; apply GlobalTheory.ses_precomp_iso_postcomp_coker_zero <;> assumption)
