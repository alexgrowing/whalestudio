import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormOfValuationProfile
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinHeightSmulInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsEvEqProdNormZpow
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicCharacterFrequenciesAndConductorProduct
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open IsDedekindDomain
open scoped nonZeroDivisors

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_norm_of_valuation_profile : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E)
    (e : HeightOneSpectrum (𝓞 E) → ℤ),
    (∀ c : Fv F v ⊗[F] E, c • y ∈ latLoc F L v ↔
        ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → GlobalTheory.UnrTate.valAt v w c ≤ WithZero.exp (-e w)) →
      (GlobalTheory.EisMidHt.normFin F L v y : ℝ) =
        ∏ w ∈ Formalism.L2.Host.aboveF (L := E) F v, (Ideal.absNorm w.asIdeal : ℝ) ^ e w := by
  first | exact @GlobalTheory.EisMidHt.normFin_eq_prod_absNorm_of_valAt | exact GlobalTheory.EisMidHt.normFin_eq_prod_absNorm_of_valAt | (intros; apply GlobalTheory.EisMidHt.normFin_eq_prod_absNorm_of_valAt <;> assumption)
