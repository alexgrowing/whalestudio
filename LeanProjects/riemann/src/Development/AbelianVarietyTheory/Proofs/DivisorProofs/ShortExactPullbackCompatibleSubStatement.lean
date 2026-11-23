import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactPullbackCompatibleSub
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackPreservesLineBundleFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactVectorBundlesRankAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsColimitCokernelCoforkBiprodMap
open CategoryTheory Limits AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortExact_pullback_compatible_sub : ∀ (X : Scheme.{0}) {A E₂ E₃ F F' : X.Modules} (b : E₂ ⟶ E₃) [Epi b] (ιF : F ⟶ E₃)
    (ι' : F' ⟶ E₃) [Mono ι'] (s : F ⟶ F'), s ≫ ι' = ιF → ∀ (f : A ⟶ E₂)
    (hz : f ≫ b ≫ cokernel.π ιF = 0), (ShortComplex.mk f (b ≫ cokernel.π ιF) hz).ShortExact →
    ∀ (t : A ⟶ pullback b ι') (τ : A ⟶ F), t ≫ pullback.fst b ι' = f →
    t ≫ pullback.snd b ι' = τ ≫ s → ∃ hz' : t ≫ pullback.snd b ι' ≫ cokernel.π s = 0,
      (ShortComplex.mk t (pullback.snd b ι' ≫ cokernel.π s) hz').ShortExact := by
  first | exact @GlobalTheory.shortExact_pullback_cokernel_modules | exact GlobalTheory.shortExact_pullback_cokernel_modules | (intros; apply GlobalTheory.shortExact_pullback_cokernel_modules <;> assumption)
