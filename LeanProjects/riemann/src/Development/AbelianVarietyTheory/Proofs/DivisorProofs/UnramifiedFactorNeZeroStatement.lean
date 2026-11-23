import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorNeZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeFinVac

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_factor_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (B : Base F E)
    (X : Chars F E) (a a' : ℕ), X.IsGood B a a' → ∀ (𝔞 : FractionalIdeal (𝓞 E)⁰ E) (k : ℕ), 1 ≤ k → ∀ v, v ∉ X.T →
      unrFac X.ν 𝔞 (k : ℂ) v ≠ 0 := by
  first | exact @GlobalTheory.UnrEuler.unrFac_nu_nat_ne_zero | exact GlobalTheory.UnrEuler.unrFac_nu_nat_ne_zero | (intros; apply GlobalTheory.UnrEuler.unrFac_nu_nat_ne_zero <;> assumption)
