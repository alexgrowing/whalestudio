import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSpanOfPluckerProportional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_of_plucker_proportional : ∀ (K : Type) [Field K] (M k : ℕ) (c c' : Fin k → Fin (M + 1) → K) (a : K), plk c' id ≠ 0 → plk c' id = a • plk c id → ∀ l, c' l ∈ Submodule.span K (Set.range c) := by
  first | exact @GlobalTheory.FlagEmb.mem_span_of_plk_eq_smul | exact GlobalTheory.FlagEmb.mem_span_of_plk_eq_smul | (intros; apply GlobalTheory.FlagEmb.mem_span_of_plk_eq_smul <;> assumption)
