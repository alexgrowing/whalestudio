import Development.AutomorphicArithmetic.ResidueCharacters.StarS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowDef
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfSetup
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowGlue

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
theorem UpperTheory.N.starSF_of_prints (hP : Hypotheses₂) : _root_.UpperTheory.N.StarSelfDualCondition := by
  obtain ⟨A, B, hA, hB, h⟩ := _root_.UpperTheory.N.exists_nonneg_c_constants_of_prints hP
  exact _root_.UpperTheory.N.starSF_of_rowC_alt A B hA hB h
end
