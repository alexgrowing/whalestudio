import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDetLeOfWeightedEntryBoundStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem norm_mixTop_le_of_weighted : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (w : Fin n → ℝ) (c : ℝ), (∀ a, 0 < w a) → (∀ i a b p q, ‖K i a b p q‖ * (w a * w b) ≤ c) → ‖mixTop K‖ ≤ (Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  intro n r _ _ K w c hw hK
  set D : ℝ := (n.factorial : ℝ) * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 with hD
  have hs : ∀ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hterm : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      ‖((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det‖ ≤ D := by
    intro p π u
    rw [norm_mul, norm_mul, hs, hs, one_mul, one_mul]
    exact GlobalTheory.T.norm_det_le_of_weighted_entry_bound _ u w c hw (fun i b => by simpa using hK i (u i) b (p i) (p (π i)))
  have hsum : ‖∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det‖ ≤
      (Fintype.card r : ℝ) ^ n * ((n.factorial : ℝ) * ((n.factorial : ℝ) * D)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun π _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun u _ => hterm p π u))).trans ?_
    simp [Finset.sum_const, Fintype.card_perm, Fintype.card_fun]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  unfold mixTop
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (n.factorial : ℝ)⁻¹ * ‖_‖ ≤ (n.factorial : ℝ)⁻¹ *
        ((Fintype.card r : ℝ) ^ n * ((n.factorial : ℝ) * ((n.factorial : ℝ) * D))) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hf.le)
    _ = _ := by rw [hD]; field_simp

end GlobalTheory.GoodTop
