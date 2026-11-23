import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAntisymmOfDoublePointSymmMultilinear
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForm_antisymm_of_doublePoint_symmMultilinear : ∀ (κ : Type) (a b : κ), a ≠ b → ∀ (A : Type) [AddCommGroup A] (n : ℕ) (T : MultilinearMap ℤ (fun _ : Fin (n + 1) => A) ℤ), (∀ (σ : Equiv.Perm (Fin (n + 1))) (y : Fin (n + 1) → A), T (y ∘ σ) = T y) → ∀ (u v : κ → A) (L : MvPolynomial κ ℝ →ₗ[ℝ] ℝ) (μ : ℤ), μ ≠ 0 → (∀ x, x ≠ a → x ≠ b → u x = v x) → u a + u b = v a + v b → (∀ s : Fin (n + 1) → κ, T (u ∘ s) = 0) → (∀ s : Fin (n + 1) → κ, T (v ∘ s) = 0) → (∀ (k : ℕ) (P : MvPolynomial κ ℝ), P.IsHomogeneous k → k ≠ n → L P = 0) → (∀ s : Fin n → κ ⊕ κ, ((T (Fin.cons (v b - u a) (Sum.elim u v ∘ s)) : ℤ) : ℝ) = μ * L (∏ i, X (Sum.elim id id (s i)))) → ∀ Q : MvPolynomial κ ℝ, L (rename (Equiv.swap a b) Q) = - L Q := by
  first | exact @GlobalTheory.FlagPush.MultiLevel.antisymm_of_multilinear | exact GlobalTheory.FlagPush.MultiLevel.antisymm_of_multilinear | (intros; apply GlobalTheory.FlagPush.MultiLevel.antisymm_of_multilinear <;> assumption)
