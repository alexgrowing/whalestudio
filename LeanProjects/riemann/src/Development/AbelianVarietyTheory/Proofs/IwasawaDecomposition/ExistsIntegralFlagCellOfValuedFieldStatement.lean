import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralFlagCellOfValuedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_flagCell_of_valuedField : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (A : ValuationSubring K) (M : ℕ) (c u : Let m → Fin (M + 1) → K), InBlock c u → (∀ τ, LinearIndependent K fun j : Fin (m τ) => u ⟨τ, j⟩) → ∃ (w : Pm m) (x : CellVar m → K) (d : Let m → K), (∀ v, x v ∈ A) ∧ (∀ z, d z ≠ 0) ∧ Tri (cellVec c w x) u d := by
  first | exact @GlobalTheory.FlagEmb.exists_integral_cell | exact GlobalTheory.FlagEmb.exists_integral_cell | (intros; apply GlobalTheory.FlagEmb.exists_integral_cell <;> assumption)
