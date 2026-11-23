import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleSystemOfLatticeMaps
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatible_system_of_lattice_maps : ∀ (L : Type) [AddCommGroup L] [Module.Finite ℤ L] (P : ℕ → (L →+ L) → Prop), (∀ (n : ℕ) (g g' : L →+ L), 0 < n → P n g → (∀ a, ∃ b, g' a - g a = n • b) → P n g') → (∀ (n m : ℕ) (g : L →+ L), 0 < n → 0 < m → P (n * m) g → P n g) → (∀ n : ℕ, 0 < n → ∃ g, P n g) → ∃ f : ℕ → L →+ L, (∀ n : ℕ, 0 < n → P n (f n)) ∧ ∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ b, f (n * m) a - f n a = n • b := by
  first | exact @GlobalTheory.exists_compatible_family_mod_of_levels | exact GlobalTheory.exists_compatible_family_mod_of_levels | (intros; apply GlobalTheory.exists_compatible_family_mod_of_levels <;> assumption)
