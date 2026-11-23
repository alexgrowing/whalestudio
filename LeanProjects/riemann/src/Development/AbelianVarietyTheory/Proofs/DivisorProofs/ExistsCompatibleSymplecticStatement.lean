import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleSymplectic
import Mathlib
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_symplectic_alt : ∀ (F : Type) [Field F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ (g : ℕ) (G : ℕ → Type) [∀ n, AddCommGroup (G n)] (e : ∀ n, G n → G n → Fˣ) (π : ∀ M n, G M →+ G n), (∀ n, 0 < n → Nonempty (G n ≃+ (Fin (2 * g) → ZMod n))) → (∀ n x y z, e n (x + y) z = e n x z * e n y z) → (∀ n x y z, e n x (y + z) = e n x y * e n x z) → (∀ n x, e n x x = 1) → (∀ n, 0 < n → ∀ x, (∀ y, e n x y = 1) → x = 0) → (∀ n m, 0 < n → 0 < m → ∀ x y, e n (π (n * m) n x) (π (n * m) n y) = e (n * m) x y ^ m) → (∀ M n k, 0 < k → 0 < M → k ∣ n → n ∣ M → ∀ x, π n k (π M n x) = π M k x) → ∃ ev : ∀ n, ((Fin g → ℤ) × (Fin g → ℤ)) →+ G n, (∀ n, 0 < n → ∀ a b, ev n a = ev n b ↔ ∃ e', a = b + n • e') ∧ (∀ n, 0 < n → Function.Surjective (ev n)) ∧ (∀ n m, 0 < n → 0 < m → ∀ a, π (n * m) n (ev (n * m) a) = ev n a) ∧ (∀ n, 0 < n → ∀ a b, e n (ev n a) (ev n b) = ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1)) := by
  first | exact @GlobalTheory.SympTower.exists_compatible_symplectic | exact GlobalTheory.SympTower.exists_compatible_symplectic | (intros; apply GlobalTheory.SympTower.exists_compatible_symplectic <;> assumption)
