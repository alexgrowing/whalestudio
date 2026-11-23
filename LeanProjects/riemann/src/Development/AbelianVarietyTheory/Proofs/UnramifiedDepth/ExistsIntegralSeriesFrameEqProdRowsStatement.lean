import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralSeriesFrameEqProdRows
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralSeries_frame_eq_prod_rows : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (Orb : Type) [Fintype Orb] (I : Orb → Fin 2 → Type) [∀ o g, Fintype (I o g)] (κ : Type) [Fintype κ] [DecidableEq κ] (X : ∀ o, RawChart C d (I o) κ) (d₀ : ℕ) (I₀ : Fin 2 → Type) [∀ g, Fintype (I₀ g)] (X₀ : RawChart C d₀ I₀ κ), RLaw X₀ V → (∀ o, (X o).ex = X₀.ex ∧ (X o).h = X₀.h ∧ (X o).k = X₀.k) → ∀ (π : Orb → Fin 2 → Matrix κ κ C) (W : Matrix κ κ C), (∀ o g, IntEnd X₀ V (π o g)) → (∀ o g c, (π o g).mulVec ((X o).u g c) = (X o).u g c) → (∀ o g o' g' c, (o, g) ≠ (o', g') → (π o g).mulVec ((X o').u g' c) = 0) → (∑ o, hEnd X₀ (π o 0) (π o 1)) - hEnd X₀ (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) ∈ logInt V κ → ∀ gr : ∀ o, MvPowerSeries (WV (I o)) C, (∀ o, gr o ∈ ExpInt (X o) V) → ∃ F : MvPowerSeries κ C, IntS V F ∧ MvPowerSeries.subst (fun x : κ => MvPowerSeries.subst (fun i : κ => ∑ w : WVO I, (X w.1).u w.2.1 w.2.2 i • (MvPowerSeries.X w : MvPowerSeries (WVO I) C)) (X₀.ex x)) (F * mvExp ((X₀.k : C) • hEnd X₀ 1 W)) = ∏ o, MvPowerSeries.subst (fun w : WV (I o) => (MvPowerSeries.X (⟨o, w⟩ : WVO I) : MvPowerSeries (WVO I) C)) (gr o * mvExp (X o).hRow) := by
  first | exact @GlobalTheory.RowVal.exists_intS_frame_eq_prod | exact GlobalTheory.RowVal.exists_intS_frame_eq_prod | (intros; apply GlobalTheory.RowVal.exists_intS_frame_eq_prod <;> assumption)
