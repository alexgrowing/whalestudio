import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramified
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_coefficient_bounded_spherical_unramified : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A) (L : Lat A), IsInfFam θ → ∀ (m : Measure (GA D A)), m.IsHaarMeasure → ∀ (Sf : Finset (FinPl D)), ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram L (Sf : Set (FinPl D)) u₁ par → SphFun A L Sf u₂ → ∀ v ∉ Sf, ∀ x : GA D A, proj D.sp.cm.sig A.gram v x = 1 → IsSphCoef A L v par fun y => rcoef m u₁ u₂ (x * emb D.sp.cm.sig A.gram v y) := by
  first | exact @GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef | exact GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef | (intros; apply GlobalTheory.Core.Rk.SphCoef.isSphCoef_rcoef <;> assumption)
