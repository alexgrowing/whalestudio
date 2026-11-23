import Mathlib
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGlobalNefBoundStatement

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem m2_of_good_tower : Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.M2 := by
  intro _ E _ _ _ _ H D Xo l c Y _ T o II hglob _ hp hq
  obtain ⟨Yl, hg, hloc, -, -, hdom⟩ := hglob
  intro B a p hpr hnS mu hmu hnef
  have hpbad : p ∉ T.bad := fun hb =>
    hnS (show Nat.Prime p ∧ (p ≤ B ∨ p ∈ T.bad) from ⟨hpr, Or.inr hb⟩)
  have h2 : 2 < p := lt_of_le_of_ne hpr.two_le (fun h => hpbad (by rw [← h]; exact T.two_mem))
  have hdisc : ¬ ((p : ℤ) ∣ NumberField.discr E) := fun hd =>
    hpbad ((o.toTowerOrigin.bad_iff p).2 ⟨hpr, dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd 2) _⟩)
  have hpS : p ∉ o.toTowerOrigin.S B := fun h => hnS ((o.toTowerOrigin.S_iff B p).1 h)
  rw [o.toTowerOrigin.j_eq] at hnef
  exact GlobalTheory.T.hodge_cpt_global_nef_bound E H D Xo Yl
    (fun p W hp hW i => ⟨((hloc p W hp hW).2 i).1, ((hloc p W hp hW).2 i).2.1⟩)
    l c hg Y hdom hp hq (o.toTowerOrigin.S B) (T.M B a) (o.toTowerOrigin.Or B a).𝔐
    (o.toTowerOrigin.Or B a).Fl (o.toTowerOrigin.Or B a).e (o.toTowerOrigin.Or B a).lines
    p hpr h2 hpS hdisc mu hmu hnef

end GlobalTheory.CompanionTheory.Ar.Top
