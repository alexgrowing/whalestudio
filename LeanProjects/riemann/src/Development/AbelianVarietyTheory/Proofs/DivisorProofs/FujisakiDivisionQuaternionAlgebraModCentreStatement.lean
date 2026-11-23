import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FujisakiDivisionQuaternionAlgebraModCentre
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fujisaki_divisionQuaternionAlgebra_mod_centre : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∀ x : ℍ[F, a, b], nrm x = 0 → x = 0) → ∃ C : Set (DA F a b), IsCompact C ∧ ∀ y : DA F a b, IsUnit (nrm y) → ∃ (δ : ℍ[F, a, b]) (l : AF F) (c c' : DA F a b), nrm δ ≠ 0 ∧ IsUnit l ∧ c ∈ C ∧ c' ∈ C ∧ c * c' = 1 ∧ c' * c = 1 ∧ y = l • (rat δ * c) := by
  first | exact @GlobalTheory.QSA.FujisakiQ.fujisaki_mod_centre | exact GlobalTheory.QSA.FujisakiQ.fujisaki_mod_centre | (intros; apply GlobalTheory.QSA.FujisakiQ.fujisaki_mod_centre <;> assumption)
