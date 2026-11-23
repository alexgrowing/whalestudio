import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ParMem
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.Top.Bl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw GlobalTheory.ShFam
open Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Mem.Th
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw
structure EllipticHypothesis : Prop where
  e1 : GlobalTheory.TwSys.Cheb
  e2 : GlobalTheory.Published.PoitouTateTotallyComplex
  e3 : GlobalTheory.Published.CohDimTwo
  e4 : GlobalTheory.Published.TameLocal
  e5 : LocalFiniteness
  e6 : LocalTateDuality
  e7 : LocalEulerChar
  e8 : GlobalFiniteness
  e9 : GlobalEulerChar
  e10 : UnramifiedOrthogonality
  e11 : BlochKatoReduction.Gen.ArchimedeanSignatureMatching
  e12 : GreenbergWiles
  e13 : GlobalTheory.Published.RayCharacterArtin
  e14 : GlobalTheory.Published.ChebotarevDegreeOne
  e15 : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator
  e16 : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat
  e17 : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt
  e18 : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt
  e19 : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform
  e20 : GlobalTheory.HeckeSupSt.HeckeReadTie
  e21 : GlobalTheory.Published.AutomorphicFormsFiniteGL
  e22 : _root_.UpperTheory.GalS.CuspUAlt
  e23 : GlobalTheory.Published.DeRhamPotSemistable
  e24 : _root_.UpperTheory.GalS.CarUAlt
  e25 : ∀ D : D7, LocalSituation.Conclusion5 D
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
def MultiplicityCondition {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : Prop :=
  GlobalTheory.Fc.EvP fun _ K => ∀ q : WPt p.s K, GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat
end
end GlobalTheory.Mem.Top.Bl
end
end
