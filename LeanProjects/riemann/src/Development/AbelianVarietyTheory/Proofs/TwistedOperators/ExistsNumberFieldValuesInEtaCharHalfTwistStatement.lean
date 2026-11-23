import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsNumberFieldValuesInEtaCharHalfTwist
import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharHost
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.AlgValsFinMain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
open NumberField IsDedekindDomain Formalism.L2.Host
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_valuesIn_etaChar_halfTwist : ∀ {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E), IsEtaT H χ → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn (1 / 2) (algebraMap M ℂ) := by
  first | exact @GlobalTheory.EtaValsNumberField.etaVals | exact GlobalTheory.EtaValsNumberField.etaVals | (intros; apply GlobalTheory.EtaValsNumberField.etaVals <;> assumption)
