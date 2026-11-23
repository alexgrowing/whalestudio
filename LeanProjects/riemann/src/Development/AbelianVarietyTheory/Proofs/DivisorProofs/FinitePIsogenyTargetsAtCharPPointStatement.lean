import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePIsogenyTargetsAtCharPPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogTarget
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_pIsogenyTargets_at_charP_point : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (c : ℕ) (M : Model b N) (u : M.X), u ∉ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))) → ∀ (L : Type) [Field L] [IsAlgClosed L] (h : M.X.residueField u →+* L), {ζ : Sp L ⟶ M.X | CorrQF.IsogTarget M c (spMap h ≫ M.X.fromSpecResidueField u) ζ}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.CorrQF.finite_isogTarget) | (exact GlobalTheory.UPel.HT.ES.CorrQF.finite_isogTarget) | (intros; apply GlobalTheory.UPel.HT.ES.CorrQF.finite_isogTarget <;> assumption)
