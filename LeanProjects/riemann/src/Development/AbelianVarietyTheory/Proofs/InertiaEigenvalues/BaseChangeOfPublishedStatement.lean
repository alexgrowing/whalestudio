import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeOfHyp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecT
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_change_of_hypotheses : GlobalTheory.Published.BaseChangeDefiniteUnitary → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → GlobalTheory.Published.DiscreteSpectrumGL → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : AUSide D), CGTrue hL D T → AUTrue hL D T A → SphericalInertData.Conclusion1 D := by
  first | exact @GlobalTheory.BaseChangeClosing.conclusion1_of_baseChange | exact GlobalTheory.BaseChangeClosing.conclusion1_of_baseChange | (intros; apply GlobalTheory.BaseChangeClosing.conclusion1_of_baseChange <;> assumption)
