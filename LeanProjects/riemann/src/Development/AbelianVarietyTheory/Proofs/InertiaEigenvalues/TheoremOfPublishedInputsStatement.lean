import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaEigenvalueTheoremOfHyp
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistAllPowersOfGaloisCohomologyClassField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_of_published_inputs : GlobalTheory.TwSys.Cheb → GlobalTheory.Published.PoitouTateTotallyComplex → GlobalTheory.Published.CohDimTwo → GlobalTheory.Published.TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → GlobalTheory.Published.RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → GlobalTheory.Published.AutomorphicFormsFiniteGL → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.GalOfCusp.LocalGlobalAboveL → (∀ D : D7, LocalSituation.Conclusion5 D) → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : GlobalTheory.Mem.Top.Bl.Prm hL), (GlobalTheory.Mem.Top.EvLgG fun K B f T => GlobalTheory.Mem.Top.Bl.KPx B f → T = GlobalTheory.Mem.Top.TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (p.N K B f T w Z Wt p0 t nch n xd c) → Nonempty (p.R K B f T w Z Wt p0 t) → GlobalTheory.Mem.Top.Bl.ColPin w → Nonempty (TwOf hL K B f T w Z Wt p0 t nch n xd c)) → GlobalTheory.Mem.Top.GroupRetwisting.ExportF GlobalTheory.Mem.Top.Bl.KPx (GlobalTheory.Mem.Top.Bl.IsBuiltE p.s) := by
  first | exact @GlobalTheory.ExportFirst.exportF_isBuiltE | exact GlobalTheory.ExportFirst.exportF_isBuiltE | (intros; apply GlobalTheory.ExportFirst.exportF_isBuiltE <;> assumption)
