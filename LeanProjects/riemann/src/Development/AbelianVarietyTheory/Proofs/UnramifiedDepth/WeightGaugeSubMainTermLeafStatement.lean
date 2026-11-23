import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightGaugeSubMainTermLeaf
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_gauge_sub_mainTerm_leaf : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → 5 ≤ V.l → ∀ (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → ∀ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (N M : ℕ) (e : Fin N → I g → C) (v' : Fin M → I (1 - g) → C) (Φt : Fin N → J g → C), (∀ c x, (X.G g).ty (Sum.inl x) ≠ a → e c x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0) → (∀ c, WtGe1 V i 0 (linPull e (t g c))) → (∀ κ : J g, (X.G g).ty (Sum.inr κ) = a + (i : ZMod d) → WtGe1 V i 0 (linPull e ((S g).ze (t g) κ) - ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, Φt δ κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i))) → WtGe2 V i (1 / ((V.l : ℝ) - 1)) (X.hM g a i e v' - mainM V i (fun b c => ∑ κ : J g, ∑ k : I (1 - g), Φt c κ * X.pair g κ k * v' b k)) := by
  first | exact @GlobalTheory.MainTermWeight.weight_gauge_sub_main | exact GlobalTheory.MainTermWeight.weight_gauge_sub_main | (intros; apply GlobalTheory.MainTermWeight.weight_gauge_sub_main <;> assumption)
