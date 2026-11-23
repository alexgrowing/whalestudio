import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD)

namespace GlobalTheory.JetExp

variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem sz_mul {r r' : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r' y) : Sz l lam (r + r') (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have e : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  rw [e, map_mul, norm_mul, Real.rpow_add hl]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r r' : ℝ} {x : ℂ} (h : r ≤ r') (hx : Sz l lam r x) : Sz l lam r' x :=
  ⟨hx.1, hx.2.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Fact.out : l.Prime).one_lt.le) h)⟩

theorem sz_one : Sz l lam 0 1 := ⟨one_mem _, by
  have e : (⟨1, one_mem _⟩ : algebraicClosure ℚ ℂ) = 1 := rfl
  rw [e, map_one, norm_one, Real.rpow_zero]⟩

theorem sz_prod {ι : Type} (t : Finset ι) (r : ι → ℝ) (f : ι → ℂ) (h : ∀ i ∈ t, Sz l lam (r i) (f i)) :
    Sz l lam (∑ i ∈ t, r i) (∏ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (sz_one (l := l) (lam := lam))
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    exact sz_mul (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem norm_factorial_inv_le (n : ℕ) : ‖((n.factorial : ℂ_[l]))‖⁻¹ ≤ (l : ℝ) ^ (n : ℝ) := by
  have hp : l.Prime := Fact.out
  have e1 : ((n.factorial : ℂ_[l])) = (((n.factorial : ℚ) : ℚ_[l]) : ℂ_[l]) := by simp
  rw [e1, PadicComplex.norm_extends', Padic.eq_padicNorm,
    padicNorm.eq_zpow_of_nonzero (by exact_mod_cast Nat.factorial_ne_zero n), padicValRat.of_nat]
  have hv : padicValNat l n.factorial ≤ n := by
    have := sub_one_mul_padicValNat_factorial (p := l) n
    have h1 : 1 ≤ l - 1 := by have := hp.two_le; omega
    calc padicValNat l n.factorial ≤ (l - 1) * padicValNat l n.factorial := Nat.le_mul_of_pos_left _ h1
      _ ≤ n := by rw [this]; exact Nat.sub_le _ _
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hp.one_lt.le
  rw [Rat.cast_zpow, Rat.cast_natCast, zpow_neg, inv_inv, zpow_natCast, Real.rpow_natCast]
  exact pow_le_pow_right₀ hl1 hv

theorem sz_factorial_inv (n : ℕ) : Sz l lam (n : ℝ) ((n.factorial : ℂ)⁻¹) := by
  have hm : ((n.factorial : ℂ)⁻¹) ∈ algebraicClosure ℚ ℂ := inv_mem (natCast_mem _ _)
  refine ⟨hm, ?_⟩
  have e : (⟨(n.factorial : ℂ)⁻¹, hm⟩ : algebraicClosure ℚ ℂ) = ((n.factorial : algebraicClosure ℚ ℂ))⁻¹ := by
    ext; simp
  rw [e, map_inv₀, map_natCast, norm_inv]
  exact norm_factorial_inv_le n

theorem expansion_of_jetInt : JetInt → Expansion := by
  classical
  intro hJ E _ _ _ _ I _ d φ s hφ hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy _ _ lam Ω hΩ
  obtain ⟨a, b, hab, hX⟩ := hJ E I d φ s hφ hs z hz 𝔣 Λ h𝔣 hΛ l hl Q hQ hQl y hy lam Ω hΩ
  refine ⟨a, b, hab, fun g κ u hg hu => ?_⟩
  have h1 := hX g κ u hg hu
  have h2 : Sz l lam ((∑ i, κ i : ℕ) : ℝ) (∏ i, ((κ i).factorial : ℂ)⁻¹) := by
    rw [Nat.cast_sum]
    exact sz_prod _ _ _ fun i _ => sz_factorial_inv (κ i)
  have e : iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / (a i ^ (2 * s) * ((κ i).factorial : ℂ))) =
      (iterD u g 0 * ∏ i, ((b i / a i) ^ κ i / a i ^ (2 * s))) * ∏ i, ((κ i).factorial : ℂ)⁻¹ := by
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_mul_eq_div_div, div_eq_mul_inv (_ / _)]
  rw [e]
  refine sz_mono ?_ (sz_mul h1 h2)
  have hK : (0 : ℝ) ≤ ((∑ i, κ i : ℕ) : ℝ) := Nat.cast_nonneg _
  split_ifs <;> nlinarith

end GlobalTheory.JetExp
