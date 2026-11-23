import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeBiadditiveSymmAdjointIntegralEnd
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
theorem _root_.GlobalTheory.T.gauge_biadditive_symm_adjoint_integralEnd : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → IntEnd X V 0 ∧ (∀ A B, IntEnd X V A → IntEnd X V B → IntEnd X V (A + B)) ∧ (∀ A B, IntEnd X V A → IntEnd X V B → IntEnd X V (A * B)) ∧ (∀ A, hEnd X A 0 = 0 ∧ hEnd X 0 A = 0) ∧ (∀ A A' B, IntEnd X V A → IntEnd X V A' → IntEnd X V B → hEnd X A B + hEnd X A' B - hEnd X (A + A') B ∈ logInt V κ ∧ hEnd X B A + hEnd X B A' - hEnd X B (A + A') ∈ logInt V κ) ∧ (∀ A B, IntEnd X V A → IntEnd X V B → hEnd X B A - hEnd X A B ∈ logInt V κ) ∧ (∀ M M' A B, IsEnd X V M M' → IntEnd X V A → IntEnd X V B → hEnd X (M * A) B - hEnd X A (M' * B) ∈ logInt V κ) := by
  first | exact @GlobalTheory.RowVal.EndCalc.end_calc | exact GlobalTheory.RowVal.EndCalc.end_calc | (intros; apply GlobalTheory.RowVal.EndCalc.end_calc <;> assumption)
