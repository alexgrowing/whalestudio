import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactOfPullbackCokernel
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitCokernelCoforkBiprodMap
open CategoryTheory Limits AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_of_pullback_cokernel : ∀ (X : Scheme.{0}) {A E₂ E₃ F : X.Modules} (b : E₂ ⟶ E₃) (ι : F ⟶ E₃) [Epi b] [Mono ι]
    (f : A ⟶ E₂) (e : A ⟶ pullback b ι) [IsIso e], f = e ≫ pullback.fst b ι →
    ∃ hz : f ≫ b ≫ cokernel.π ι = 0, (ShortComplex.mk f (b ≫ cokernel.π ι) hz).ShortExact := by
  first | exact @GlobalTheory.PullbackSub.shortExact_preimage_of_epi_mono | exact GlobalTheory.PullbackSub.shortExact_preimage_of_epi_mono | (intros; apply GlobalTheory.PullbackSub.shortExact_preimage_of_epi_mono <;> assumption)
