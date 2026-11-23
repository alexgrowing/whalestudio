import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGenericFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonemptyCptOverOfFlatPreimmersion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonMiddle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameLawsOfModuli
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ExpBCChart
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.CombMap

theorem isCombAt_spMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S T : Type) [CommRing S] [CommRing T] (φ : S →+* T) (x : Sp S ⟶ Xo.X) (m : ℕ) (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsCombAt x v cf w → IsCombAt (spMap φ ≫ x) (fun i => spMap (Formalism.L2.Pj.dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (Formalism.L2.Pj.dualMap φ) ≫ w) := by
  intro E _ _ _ H Dw l Xo S T _ _ φ x m v cf w hc
  obtain ⟨u, hu, hw⟩ := hc
  have hcomp : (Formalism.L2.Pj.dualMap φ).comp (algebraMap S (DualNumber S)) =
      (algebraMap T (DualNumber T)).comp φ := by
    ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let f : tEps (spMap φ ≫ x) ⟶ tEps x := Over.homMk (spMap (Formalism.L2.Pj.dualMap φ)) (by
    show spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap T (DualNumber T)) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, hcomp,
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, Category.assoc])
  let P : (tEps x ⟶ Xo.univ.t.G) →* (tEps (spMap φ ≫ x) ⟶ Xo.univ.t.G) :=
    { toFun := fun g => f ≫ g
      map_one' := CategoryTheory.MonObj.comp_one f
      map_mul' := CategoryTheory.MonObj.comp_mul f }
  refine ⟨fun i => f ≫ u i, fun i => ?_, ?_⟩
  · rw [Over.comp_left, hu i]
    show spMap (Formalism.L2.Pj.dualMap φ) ≫ spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (cf i)) ≫ v i =
      spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (φ (cf i))) ≫ spMap (Formalism.L2.Pj.dualMap φ) ≫ v i
    rw [← Category.assoc, ← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp,
      ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
    congr 2
    ext y <;> simp [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, smul_eq_mul, map_mul,
      TrivSqZeroExt.algebraMap_eq_inl]
  · have h1 : (List.ofFn fun i => f ≫ u i) = (List.ofFn u).map P := by
      rw [List.map_ofFn]
      rfl
    rw [h1, ← map_list_prod]
    show (f ≫ (List.ofFn u).prod).left = _
    rw [Over.comp_left, hw]
    rfl

end GlobalTheory.CompanionTheory.Ar.CombMap
