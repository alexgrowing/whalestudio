import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFirstFromResolutionAndGaga
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_evaluation_hom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∀ e : ℕ, ∃ ev : D.La → (Over.mk x ⟶ o.A), (∀ y z, ev (y + z) = ev y * ev z) ∧ (∀ (c : D.O) y, ev (c • y) = ev y ≫ o.act.act c) ∧ (∀ y, ev y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev y = q) := by
  first | (exact @GlobalTheory.UPel.HT.PTors.exists_ev_pow) | (exact GlobalTheory.UPel.HT.PTors.exists_ev_pow) | (intros; apply GlobalTheory.UPel.HT.PTors.exists_ev_pow  <;> assumption)
