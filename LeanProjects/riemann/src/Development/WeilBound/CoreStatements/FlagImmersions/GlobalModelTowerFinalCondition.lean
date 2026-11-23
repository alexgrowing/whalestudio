import Development.WeilBound.CoreStatements.FlagImmersions.RootFlatOnHodgeOf
import Development.WeilBound.CoreStatements.FlagImmersions.CptEx
import Development.WeilBound.CoreStatements.FlagImmersions.HostRd
import Development.WeilBound.CoreStatements.FlagImmersions.RangeSubIff
import Development.WeilBound.CoreStatements.FlagImmersions.UnitAtOfSpan
import Development.WeilBound.CoreStatements.FlagImmersions.ExistsLiftGenFibre
import Development.WeilBound.CoreStatements.FlagImmersions.MemGenFibre
import Development.WeilBound.CoreStatements.FlagImmersions.ValAtOfExtends
import Development.WeilBound.CoreStatements.FlagImmersions.ExistsIntProj
import Development.WeilBound.CoreStatements.FlagImmersions.LocalCmpOf
import Development.WeilBound.CoreStatements.FlagImmersions.LogIdealNonpos
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

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace RootFieldNumerics

theorem rootFlatOnHodge (hFD : Fl.FlatDegree) (hG : Given) : Flat.RootFlatOnHodge :=
  RF.rootFlatOnHodge_of RF.cptEx RF.periodOf RF.smoothLine
    (RF.localCmp_of RF.pointEx RF.valuePhi RF.intFrames RF.fibSandwich) RF.chiEx RF.numerics hFD hG

theorem global_model_tower_final_condition : Fl.FlatDegree → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ a τ, ∃ R : Flat.RootFlat (T.M 2 a) τ, Flat.NearRecord (D.p + D.q) T.bad (hostRd E) (hostLval H) R.ht := by
  intro hFD hG E _ _ _ _ H D Xo l c Y _ T o II hY _ _ _ _ a τ
  exact Flat.OnHodge.tower (rootFlatOnHodge hFD hG) hY ⟨o.toTowerOrigin, o.omVB⟩ a τ

end RootFieldNumerics
