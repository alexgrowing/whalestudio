import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.DivSq

theorem four_factors {n x y : ℕ} (hx : x ∣ n) (hy : y ∣ n) (hn : n ≠ 0) :
    ∃ a b c e : ℕ, a * b * c * e = n ∧ a * b = x ∧ a * c = y := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hn (by simpa using hx)
  obtain ⟨e, he⟩ := Nat.lcm_dvd hx hy
  obtain ⟨b, hb⟩ := Nat.gcd_dvd_left x y
  obtain ⟨c, hc⟩ := Nat.gcd_dvd_right x y
  refine ⟨Nat.gcd x y, b, c, e, ?_, hb.symm, hc.symm⟩
  have hg : 0 < Nat.gcd x y := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hx0)
  have h1 := Nat.gcd_mul_lcm x y
  have h2 : Nat.gcd x y * b * c = Nat.lcm x y := by
    apply Nat.eq_of_mul_eq_mul_left hg
    rw [h1]
    calc Nat.gcd x y * (Nat.gcd x y * b * c) = (Nat.gcd x y * b) * (Nat.gcd x y * c) := by ring
      _ = x * y := by rw [← hb, ← hc]
  rw [h2, ← he]

theorem inv_rpow_natCast_mul (p : ℝ) (a b : ℕ) :
    ((((a * b : ℕ)) : ℝ) ^ p)⁻¹ = ((a : ℝ) ^ p)⁻¹ * ((b : ℝ) ^ p)⁻¹ := by
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity), mul_inv]

theorem sum_range_le_pow (p : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ p
      ≤ (∑ n ∈ Finset.range N, ((n : ℝ) ^ p)⁻¹) ^ 4 := by
  classical
  set I := Finset.range N with hI
  let φ : ℕ × ℕ × ℕ × ℕ → (Σ _ : ℕ, ℕ × ℕ) :=
    fun q => ⟨q.1 * q.2.1 * q.2.2.1 * q.2.2.2, q.1 * q.2.1, q.1 * q.2.2.1⟩
  let w : (Σ _ : ℕ, ℕ × ℕ) → ℝ := fun s => ((s.1 : ℝ) ^ p)⁻¹
  have hw : ∀ s, 0 ≤ w s := fun s => by simp only [w]; positivity
  have h1 : ∑ n ∈ I, ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ p
      = ∑ s ∈ I.sigma (fun n => n.divisors ×ˢ n.divisors), w s := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [w, Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    push_cast
    ring
  have h2 : I.sigma (fun n => n.divisors ×ˢ n.divisors) ⊆ (I ×ˢ I ×ˢ I ×ˢ I).image φ := by
    rintro ⟨n, x, y⟩ hs
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisors, hI, Finset.mem_range] at hs
    obtain ⟨hnN, ⟨hx, hn⟩, hy, -⟩ := hs
    obtain ⟨a, b, c, e, rfl, rfl, rfl⟩ := four_factors hx hy hn
    have key : ∀ d, d ∣ a * b * c * e → d ∈ I := fun d hd => by
      rw [hI, Finset.mem_range]
      exact lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hnN
    refine Finset.mem_image.2 ⟨(a, b, c, e), ?_, rfl⟩
    simp only [Finset.mem_product]
    exact ⟨key _ ⟨b * c * e, by ring⟩, key _ ⟨a * c * e, by ring⟩, key _ ⟨a * b * e, by ring⟩,
      key _ ⟨a * b * c, by ring⟩⟩
  have h3 : ∑ s ∈ (I ×ˢ I ×ˢ I ×ˢ I).image φ, w s ≤ ∑ q ∈ I ×ˢ I ×ˢ I ×ˢ I, w (φ q) :=
    Finset.sum_image_le_of_nonneg (fun s _ => hw s)
  have h4 : ∑ q ∈ I ×ˢ I ×ˢ I ×ˢ I, w (φ q) = (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) ^ 4 := by
    have : (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) ^ 4 = (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) *
      ((∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) * ((∑ n ∈ I, ((n : ℝ) ^ p)⁻¹) * (∑ n ∈ I, ((n : ℝ) ^ p)⁻¹))) := by
      ring
    rw [this]
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_product, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_product, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [w, φ]
    rw [inv_rpow_natCast_mul, inv_rpow_natCast_mul, inv_rpow_natCast_mul]
    ring
  rw [h1, ← h4]
  exact (Finset.sum_le_sum_of_subset_of_nonneg h2 fun s _ _ => hw s).trans h3

theorem summable_card_divisors_sq_div_rpow :
    ∀ s : ℝ, 0 < s → Summable fun n : ℕ => ((n.divisors.card : ℝ)) ^ 2 / (n : ℝ) ^ (1 + s) := by
  intro s hs
  have hz : Summable fun n : ℕ => ((n : ℝ) ^ (1 + s))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  refine summable_of_sum_range_le (c := (∑' n : ℕ, ((n : ℝ) ^ (1 + s))⁻¹) ^ 4)
    (fun n => by positivity) fun N => ?_
  refine (sum_range_le_pow (1 + s) N).trans ?_
  exact pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => by positivity)
    (hz.sum_le_tsum _ fun n _ => by positivity) 4

end GlobalTheory.DivSq
