import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartMapLocalSystem
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_map_local_system : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}, p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Z : Mdl Y i₀) (a : Fin Z.m), ∃ g : Sp Γ(Z.X, (Z.U a).1) ⟶ (Xo Z.i.l).XF Z.i.c, g ≫ (Y Z.i).j = Z.chart a ≫ Z.π ∧ g ≫ pullback.snd _ _ = spMap (Z.alg a) := by
  first | exact @GlobalTheory.LocM.ChartLift.exists_lift | exact GlobalTheory.LocM.ChartLift.exists_lift | (intros; apply GlobalTheory.LocM.ChartLift.exists_lift <;> assumption)
