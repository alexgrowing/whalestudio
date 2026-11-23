import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
import Development.WeilBound.CoreStatements.VolumeEquality.DegPushPF

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace LevelTowerAlt

open SheetDecomposition.PF

theorem ii_cst_int {K : Type} [Fintype K] {J : K → Type} [∀ b, Fintype (J b)] {II : IntersectionSystem}
    (hII : IsIntersectionSystem II) {P : Ideal (MRing J)} {e : ℕ} (ha : IsArithVar P (e + 1)) (A : Fin e → HermLine J)
    (hs : ∀ j, IsSmoothHerm (A j)) :
    II K J P (e + 1) (Fin.snoc (α := fun _ => HermLine J) A (cst J)) =
      -ptsIntegral (e := e) P (fun i z => Real.log ((A i).h z)) (fun _ => 1) := by
  classical
  have h1 := (hII K J).2.2 _ e A (cst J) 1 (fun _ => 0) ha hs cst_smooth (fun _ => rfl)
    Geo.isMultiHomog_one ((Ideal.ne_top_iff_one _).1 ha.2.1.1.ne_top)
  have h3 : logNorm (cst J) 1 = fun _ => 1 := by
    funext z
    simp [logNorm, SheetDecomposition.PF.cst, HermLine.ofWeight]
  refine h1.trans ?_
  rw [recR, Geo.divSupp_one, finsum_mem_empty, zero_sub, arInt, h3]

theorem snoc_cst_smooth {K : Type} [Fintype K] {J : K → Type} [∀ b, Fintype (J b)] {e : ℕ} (A : Fin e → HermLine J)
    (hs : ∀ j, IsSmoothHerm (A j)) (j : Fin (e + 1)) : IsSmoothHerm (Fin.snoc (α := fun _ => HermLine J) A (cst J) j) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa using cst_smooth
  · simpa using hs j

end LevelTowerAlt
