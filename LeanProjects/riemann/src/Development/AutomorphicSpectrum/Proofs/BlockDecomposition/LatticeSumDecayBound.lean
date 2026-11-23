import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiDimensional
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Count

theorem one_dim_step (b x : ℝ) (hb : 0 < b) (hx : 0 ≤ x) :
    ((1 + (x + 1) / b) ^ 2)⁻¹ ≤ b ^ 2 / (b + x) - b ^ 2 / (b + x + 1) := by
  have h1 : 0 < b + x := by linarith
  have h2 : 0 < b + x + 1 := by linarith
  have e1 : (1 + (x + 1) / b) = (b + x + 1) / b := by field_simp; ring
  have e2 : b ^ 2 / (b + x) - b ^ 2 / (b + x + 1) = b ^ 2 / ((b + x) * (b + x + 1)) := by
    field_simp; ring
  rw [e1, e2, div_pow, inv_div]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith

theorem one_dim_partial (b : ℝ) (hb : 0 < b) (N : ℕ) :
    ∑ k ∈ Finset.range N, ((1 + ((k : ℝ) + 1) / b) ^ 2)⁻¹ ≤ b - b ^ 2 / (b + N) := by
  induction N with
  | zero =>
    have : b ^ 2 / (b + ((0 : ℕ) : ℝ)) = b := by
      simp only [Nat.cast_zero, add_zero]; field_simp
    rw [Finset.range_zero, Finset.sum_empty, this, sub_self]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have := one_dim_step b N hb (Nat.cast_nonneg N)
    push_cast
    have e : b + ((N : ℝ) + 1) = b + N + 1 := by ring
    rw [e]
    linarith

theorem one_dim_nat (b : ℝ) (hb : 0 < b) :
    ∑' k : ℕ, ENNReal.ofReal (((1 + ((k : ℝ) + 1) / b) ^ 2)⁻¹) ≤ ENNReal.ofReal b := by
  rw [ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun N => ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have := one_dim_partial b hb N
  have h3 : 0 ≤ b ^ 2 / (b + N) := by positivity
  linarith

theorem one_dim (b : ℝ) (hb : 0 < b) :
    ∑' n : ℤ, ENNReal.ofReal (((1 + |(n : ℝ)| / b) ^ 2)⁻¹) ≤ ENNReal.ofReal (1 + 2 * b) := by
  set f : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal (((1 + |(n : ℝ)| / b) ^ 2)⁻¹) with hf
  have hsplit : HasSum f ((∑' n : ℕ, f n) + ∑' n : ℕ, f (-((n : ℤ) + 1))) :=
    HasSum.of_nat_of_neg_add_one ENNReal.summable.hasSum ENNReal.summable.hasSum
  have hneg : ∀ n : ℕ, f (-((n : ℤ) + 1)) =
      ENNReal.ofReal (((1 + ((n : ℝ) + 1) / b) ^ 2)⁻¹) := by
    intro n
    have : |(((-((n : ℤ) + 1) : ℤ)) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_neg, abs_of_nonneg (by positivity)]
    simp only [hf, this]
  have hpos : ∀ n : ℕ, f ((n + 1 : ℕ) : ℤ) =
      ENNReal.ofReal (((1 + ((n : ℝ) + 1) / b) ^ 2)⁻¹) := by
    intro n
    have : |((((n + 1 : ℕ) : ℤ)) : ℝ)| = (n : ℝ) + 1 := by
      push_cast
      rw [abs_of_nonneg (by positivity)]
    simp only [hf, this]
  have h0 : f ((0 : ℕ) : ℤ) = 1 := by simp [hf]
  have hN := one_dim_nat b hb
  have hz : ∑' n : ℕ, f n ≤ 1 + ENNReal.ofReal b := by
    rw [ENNReal.tsum_eq_iSup_nat]
    refine iSup_le fun N => ?_
    cases N with
    | zero => simp
    | succ N =>
      rw [Finset.sum_range_succ', h0, add_comm]
      gcongr
      calc ∑ k ∈ Finset.range N, f ((k + 1 : ℕ) : ℤ)
          ≤ ∑' k : ℕ, f ((k + 1 : ℕ) : ℤ) := ENNReal.sum_le_tsum _
        _ ≤ ENNReal.ofReal b := by rw [tsum_congr hpos]; exact hN
  rw [hsplit.tsum_eq, tsum_congr hneg]
  calc _ ≤ 1 + ENNReal.ofReal b + ENNReal.ofReal b := add_le_add hz hN
    _ = ENNReal.ofReal (1 + 2 * b) := by
      rw [two_mul, ← add_assoc, ENNReal.ofReal_add (by positivity) hb.le,
        ENNReal.ofReal_add (by norm_num) hb.le, ENNReal.ofReal_one]

theorem multi_dim {P : Type} [Fintype P] (g : P → ℤ → ℝ≥0∞) :
    ∑' x : P → ℤ, ∏ p, g p (x p) ≤ ∏ p, ∑' n, g p n :=
  _root_.UpperTheory.Reformulated.B.MultiDimensional.multi_dim g

theorem tsum_le_prod_of_injOn {S P : Type} [Fintype P] (m : S → P → ℤ) (b : P → ℝ)
    (hb : ∀ p, 0 < b p) (h : S → ℝ≥0∞) (hinj : Set.InjOn m {ξ | h ξ ≠ 0})
    (hh : ∀ ξ, h ξ ≤ ∏ p, ENNReal.ofReal (((1 + |(m ξ p : ℝ)| / b p) ^ 2)⁻¹)) :
    ∑' ξ, h ξ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) := by
  set g : P → ℤ → ℝ≥0∞ := fun p n => ENNReal.ofReal (((1 + |(n : ℝ)| / b p) ^ 2)⁻¹) with hg
  have hsupp : ∑' ξ, h ξ = ∑' ξ : {ξ | h ξ ≠ 0}, h ξ :=
    (tsum_subtype_eq_of_support_subset (f := h) (s := {ξ | h ξ ≠ 0})
      (fun _ hx => hx)).symm
  have hinj' : Function.Injective (fun ξ : {ξ | h ξ ≠ 0} => m ξ) :=
    fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy)
  calc ∑' ξ, h ξ = ∑' ξ : {ξ | h ξ ≠ 0}, h ξ := hsupp
    _ ≤ ∑' ξ : {ξ | h ξ ≠ 0}, (fun x : P → ℤ => ∏ p, g p (x p)) (m ξ) :=
        ENNReal.tsum_le_tsum fun ξ => hh ξ
    _ ≤ ∑' x : P → ℤ, ∏ p, g p (x p) :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj' _
    _ ≤ ∏ p, ∑' n, g p n := multi_dim g
    _ ≤ ∏ p, ENNReal.ofReal (1 + 2 * b p) :=
        Finset.prod_le_prod' fun p _ => one_dim (b p) (hb p)

end GlobalTheory.CompanionTheory.Count
