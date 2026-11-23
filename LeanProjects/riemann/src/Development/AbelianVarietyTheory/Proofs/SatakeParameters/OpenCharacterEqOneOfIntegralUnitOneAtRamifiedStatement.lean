import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OpenCharacterEqOneOfIntegralUnitOneAtRamified
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubOneMemMapOfEq
open NumberField IsDedekindDomain Formalism.L2.DIV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.openCharacter_eq_one_of_integralUnit_one_at_ramified : ∀ (F E L : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field L] (σ : L →+* ℂ) (ξ : Chr F E L), ξ ∈ openChr F E L → (ratId F E).range ≤ ξ.ker → ∀ x ∈ intU F E, (∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) ∈ Qprime ξ → GlobalTheory.Mem.Col2.afIso F E (x : AfE F E) P = 1) → ξ x = 1 := by
  first | exact @GlobalTheory.UnitCut.map_eq_one_of_one_at_ramified | exact GlobalTheory.UnitCut.map_eq_one_of_one_at_ramified | (intros; apply GlobalTheory.UnitCut.map_eq_one_of_one_at_ramified <;> assumption)
