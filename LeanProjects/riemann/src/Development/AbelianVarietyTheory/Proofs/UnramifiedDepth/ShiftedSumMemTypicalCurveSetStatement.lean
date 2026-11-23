import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ShiftedSumMemTypicalCurveSet
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shiftedSum_mem_typicalCurveSet : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ g (y : ℕ → ℕ → I g ⊕ JJ I g → C), (∀ s, y s ∈ X.TySet V g) → sumV y ∈ X.TySet V g := by
  first | exact @GlobalTheory.RowLaw.ShiftSum.sumV_mem_tySet | exact GlobalTheory.RowLaw.ShiftSum.sumV_mem_tySet | (intros; apply GlobalTheory.RowLaw.ShiftSum.sumV_mem_tySet <;> assumption)
