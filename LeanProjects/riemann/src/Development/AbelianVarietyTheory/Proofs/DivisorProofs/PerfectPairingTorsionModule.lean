import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftSystemRealStructure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfect_pairing_torsion_module : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → (∃ e : ℕ, c = p ^ e) → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 D.F) M] [Finite M], (∀ x : M, c • x = 0) → ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (e : M → M → kˣ), (∀ x x' y, e (x + x') y = e x y * e x' y) → (∀ x y y', e x (y + y') = e x y * e x y') → (∀ (a : 𝓞 D.F) x y, e (a • x) y = e x (D.bar a • y)) → (∀ x y, e x y * e y x = 1) → (∀ x, (∀ y, e x y = 1) → x = 0) → Ideal.absNorm w ^ j ≤ Nat.card {x : M // ∀ a ∈ w, a • x = 0} → ∃ H : Submodule (𝓞 D.F) M, (∀ x ∈ H, ∀ y ∈ H, e x y = 1) ∧ (∀ x, (∀ y ∈ H, e x y = 1) → x ∈ H) ∧ (∀ x ∈ H, (∃ i : ℕ, ∀ a ∈ uIdeal D r ^ i, a • x = 0) → ∀ a ∈ w, a • x = 0) ∧ Nat.card {x : M // x ∈ H ∧ ∀ a ∈ w, a • x = 0} = Ideal.absNorm w ^ j := by
  first | (exact @GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type) | (exact GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type) | (intros; apply GlobalTheory.UPel.HT.ES.exists_maximal_isotropic_of_type  <;> assumption)
