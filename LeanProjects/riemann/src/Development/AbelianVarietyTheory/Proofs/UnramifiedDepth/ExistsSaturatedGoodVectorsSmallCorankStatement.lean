import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSaturatedGoodVectorsSmallCorank
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_saturated_good_vectors_small_corank : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] [DecidableEq I] (G : Cart V d I J) (a : ZMod d), ∃ (N : ℕ) (w : Fin N → I → C) (x : Fin N → ℕ → I ⊕ J → C), (∀ ν, G.Good a (w ν) (x ν)) ∧ (∀ ν c, G.ty (Sum.inl c) ≠ a → w ν c = 0) ∧ IsSat V w ∧ (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a).card ≤ N + (Finset.univ.filter fun c : I => G.ty (Sum.inl c) = a + 1).card := by
  first | exact @GlobalTheory.GoodCorank.exists_good_sat | exact GlobalTheory.GoodCorank.exists_good_sat | (intros; apply GlobalTheory.GoodCorank.exists_good_sat <;> assumption)
