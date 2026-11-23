import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContentIdealLocalValuationBound
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
theorem _root_.GlobalTheory.T.content_ideal_local_valuation_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ u : Fin n → E, u ≠ 0 →
    ∀ I : FractionalIdeal (𝓞 E)⁰ E, I ≠ 0 → (∀ c : E, c ∈ I ↔ c • u ∈ L) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v ⊗[F] E),
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
          GlobalTheory.UnrTate.valAt v w c ≤ WithZero.exp (-FractionalIdeal.count E w I)) →
      (c • fun i => (1 : Fv F v) ⊗ₜ[F] u i) ∈ latLoc F L v := by
  first | exact @GlobalTheory.LatLine.smul_one_tmul_mem_latLoc | exact GlobalTheory.LatLine.smul_one_tmul_mem_latLoc | (intros; apply GlobalTheory.LatLine.smul_one_tmul_mem_latLoc <;> assumption)
