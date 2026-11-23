import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RingHomEqOfCongruentIntegralUnramified
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_eq_of_congruent_integral_unramified : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ), 0 < d → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) → ∀ ψ φ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, V.Ge 0 (φ x)) → V.MM (ψ ε - 1) → (∀ x, V.MM (ψ x - φ x)) → ψ = φ := by
  first | exact @GlobalTheory.CongruentCharacters.eq_of_congruent | exact GlobalTheory.CongruentCharacters.eq_of_congruent | (intros; apply GlobalTheory.CongruentCharacters.eq_of_congruent <;> assumption)
