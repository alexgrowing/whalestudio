import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DiagonalSplit
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
theorem _root_.GlobalTheory.T.sum_hEnd_sub_hEnd_mem_logInt : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] [DecidableEq κ] (X : RawChart C d I κ), RLaw X V → ∀ (Orb : Type) [Fintype Orb] (π : Orb → Fin 2 → Matrix κ κ C) (W W' : Matrix κ κ C), (∀ o g, IntEnd X V (π o g)) → IsEnd X V W W' → W + W' = 1 → (∀ o g o' g', ¬ (o = o' ∧ g' = 1 - g) → hEnd X (π o g) (W * π o' g') ∈ logInt V κ) → (∑ o, hEnd X (π o 0) (π o 1)) - hEnd X (∑ o, ∑ g, π o g) (W * ∑ o, ∑ g, π o g) ∈ logInt V κ := by
  first | exact @GlobalTheory.RowVal.MapSumDiagonal.diagonal_split | exact GlobalTheory.RowVal.MapSumDiagonal.diagonal_split | (intros; apply GlobalTheory.RowVal.MapSumDiagonal.diagonal_split <;> assumption)
