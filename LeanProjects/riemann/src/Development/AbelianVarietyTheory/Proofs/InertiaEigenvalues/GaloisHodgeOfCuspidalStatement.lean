import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_hodge_of_cuspidal : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.GalOfCusp.LocalGlobalAboveL → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), CGTrue hL D T → GlobalTheory.TripleLocal.GalHodge D T ∧ GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GaloisReps D := by
  first | exact @GlobalTheory.HodgeOfTrue.galHodge_galoisReps_of_cgTrue | exact GlobalTheory.HodgeOfTrue.galHodge_galoisReps_of_cgTrue | (intros; apply GlobalTheory.HodgeOfTrue.galHodge_galoisReps_of_cgTrue <;> assumption)
