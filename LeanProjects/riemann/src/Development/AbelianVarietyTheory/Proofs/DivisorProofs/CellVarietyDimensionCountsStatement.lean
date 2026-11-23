import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellVarietyDimensionCounts
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_variety_dimension_counts : ∀ (ι : Type) [Fintype ι] (N : ℕ), Nat.card (CellVar (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd) = dimFl ι N ∧ (∀ j : Fin (N + 1), Nat.card (CellVar (id : ι → ι) (fun _ => j)) = dimGr ι N j) ∧ ∀ x : ι × Fin (N + 1), 0 < (x.2 : ℕ) → (x.2 : ℕ) < N → Nat.card (CellVar (fun y : {y // y ≠ x} => y.1.1) (fun y => y.1.2)) + 1 = dimFl ι N := by
  first | exact @GlobalTheory.FlagZ.Count.card_cellVar | exact GlobalTheory.FlagZ.Count.card_cellVar | (intros; apply GlobalTheory.FlagZ.Count.card_cellVar <;> assumption)
