import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws3
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniformisationLawsOfBaseChangeLaws
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws5
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsSixthOfUnifUniq

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem laws_third_to_sixth_of_laws :
    Laws → DVR.TwistBaseChangeStatement → Laws3 ∧ Laws4 ∧ Laws5 ∧ Laws6 :=
  fun h ht =>
    ⟨laws3, uniformisationLaws_of_baseChange_laws h.polBaseChange h.globalFns h.secBaseChange ht,
      laws5 h.globalFns h.secBaseChange,
      lawsSixth_of_unifUniq h.globalFns h.secBaseChange h.ample⟩

end GlobalTheory
