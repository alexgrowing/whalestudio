import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKernelsPIsogeniesHarrisTaylorCharP
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsStableFlag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_kernels_pIsogenies_harrisTaylor_charP : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (c : ℕ) (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (s : Sp k ⟶ Sp R) (o : Obj b N s), Set.Finite {P : ∀ T : Over (Sp k), (T ⟶ o.A) → Prop | ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ P = fun T x => x ≫ ψ = 1} := by
  first | (exact @GlobalTheory.UPel.HT.ES.KerFin.finite_kernels) | (exact GlobalTheory.UPel.HT.ES.KerFin.finite_kernels) | (intros; apply GlobalTheory.UPel.HT.ES.KerFin.finite_kernels  <;> assumption)
