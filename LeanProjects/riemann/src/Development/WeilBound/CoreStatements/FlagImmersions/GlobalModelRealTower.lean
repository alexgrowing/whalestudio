import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.WeilBound.CoreStatements.FlagImmersions.ContAtOfHoloOn
import Development.WeilBound.CoreStatements.FlagImmersions.AnalyticAtAeval
import Development.WeilBound.CoreStatements.FlagImmersions.HasPerConj
import Development.WeilBound.CoreStatements.FlagImmersions.ExistsModelOfEq
import Development.WeilBound.CoreStatements.FlagImmersions.NormDetEq
import Development.WeilBound.CoreStatements.FlagImmersions.PerCoord
import Development.WeilBound.CoreStatements.FlagImmersions.ExistsRightInv
import Development.WeilBound.CoreStatements.FlagImmersions.RankLem
import Development.WeilBound.CoreStatements.FlagImmersions.EqZeroOfTri
import Development.WeilBound.CoreStatements.FlagImmersions.GenRigidOf
import Development.WeilBound.CoreStatements.FlagImmersions.CountableBall
import Development.WeilBound.CoreStatements.FlagImmersions.CoordsOrbit
import Development.WeilBound.CoreStatements.FlagImmersions.IsHolToOfLocal
import Development.WeilBound.CoreStatements.FlagImmersions.Imports
import Development.WeilBound.CoreStatements.FlagImmersions.FlagImmersion

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

theorem RootFieldNumerics.global_model_real_tower : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → (realOf o.toTowerOrigin).Unif := by
  intro hG E _ _ _ _ H D Xo l c Y _ T o II _ _ _ hp _ a
  rw [o.j_eq]
  exact RootFieldNumerics.Un.unif_of (RootFieldNumerics.biholo_of RootFieldNumerics.descend) RootFieldNumerics.locPer RootFieldNumerics.transport RootFieldNumerics.frameVals
    (RootFieldNumerics.perMat_of RootFieldNumerics.perCoord RootFieldNumerics.matStep) (RootFieldNumerics.flagImm_of RootFieldNumerics.rankLem)
    (RootFieldNumerics.countGen_of (RootFieldNumerics.genRigid_of RootFieldNumerics.frameVals)) RootFieldNumerics.potLoc RootFieldNumerics.ptsFam hG (le_add_right hp) (o.refOr a)
    (o.ref_top a) (o.ref_deg a) (o.ample a)
