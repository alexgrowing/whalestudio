import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesCoeffsInIdealPowEqFactorialMulStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.KatzCongr

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

def coeffIdeal (τ : Type) (J : Ideal B) : Ideal (MvPowerSeries τ B) where
  carrier := {w | ∀ α, coeff α w ∈ J}
  add_mem' ha hb α := by rw [map_add]; exact J.add_mem (ha α) (hb α)
  zero_mem' α := by rw [map_zero]; exact J.zero_mem
  smul_mem' c x hx α := by
    classical
    rw [smul_eq_mul, coeff_mul]
    exact J.sum_mem fun _ _ => J.mul_mem_left _ (hx _)

def scaledIdeal (τ : Type) (K : Ideal B) (c : Q) : Ideal (MvPowerSeries τ B) where
  carrier := {x | ∀ γ, ∃ b ∈ K, c * algebraMap B Q (coeff γ x) = algebraMap B Q b}
  add_mem' {x y} hx hy γ := by
    obtain ⟨a, ha, ea⟩ := hx γ
    obtain ⟨b, hb, eb⟩ := hy γ
    exact ⟨a + b, K.add_mem ha hb, by rw [map_add, map_add, mul_add, ea, eb, map_add]⟩
  zero_mem' γ := ⟨0, K.zero_mem, by simp⟩
  smul_mem' r x hx γ := by
    classical
    rw [smul_eq_mul, coeff_mul, map_sum, Finset.mul_sum]
    have key : ∀ q ∈ Finset.HasAntidiagonal.antidiagonal γ, ∃ b ∈ K,
        c * algebraMap B Q (coeff q.1 r * coeff q.2 x) = algebraMap B Q b := by
      intro q _
      obtain ⟨b, hb, eb⟩ := hx q.2
      exact ⟨coeff q.1 r * b, K.mul_mem_left _ hb, by rw [map_mul, map_mul, ← eb]; ring⟩
    choose! g hg eg using key
    exact ⟨∑ q ∈ Finset.HasAntidiagonal.antidiagonal γ, g q, K.sum_mem hg, by
      rw [map_sum]; exact Finset.sum_congr rfl eg⟩

end GlobalTheory.KatzCongr

namespace GlobalTheory.KatzCongr

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {τ : Type} {J : Ideal B}

theorem pow_add_sub_pow
    (hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n → ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y)
    (v w : MvPowerSeries τ B) (hw : w ∈ coeffIdeal τ J) (n : ℕ) :
    ∃ z ∈ coeffIdeal τ J, (v + w) ^ n - v ^ n = (n : MvPowerSeries τ B) * z := by
  cases n with
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | succ m =>
    choose! y hy ey using fun k (hk : 0 < k) => hdp w hw k hk
    refine ⟨∑ k ∈ Finset.range (m + 1), (m.descFactorial k : MvPowerSeries τ B) * y (k + 1) * v ^ (m - k),
      Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (hy _ (Nat.succ_pos k))), ?_⟩
    rw [add_comm v w, add_pow, Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_zero, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, add_sub_cancel_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h : (((k + 1).factorial * (m + 1).choose (k + 1) : ℕ) : MvPowerSeries τ B) =
        ((m + 1 : ℕ) : MvPowerSeries τ B) * (m.descFactorial k : ℕ) := by
      rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.succ_descFactorial_succ, Nat.cast_mul]
    rw [ey (k + 1) (Nat.succ_pos k), Nat.add_sub_add_right]
    push_cast at h ⊢
    linear_combination (y (k + 1) * v ^ (m - k)) * h

theorem prod_sub_mem {σ : Type} (K : Ideal B) (c : Q) (α : σ →₀ ℕ) (u v : σ → MvPowerSeries τ B)
    (hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n → ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y)
    (huv : ∀ i, u i - v i ∈ coeffIdeal τ J)
    (hsc : ∀ i, ∀ z ∈ coeffIdeal τ J, (α i : MvPowerSeries τ B) * z ∈ scaledIdeal τ K c)
    (s : Finset σ) : ∏ i ∈ s, u i ^ α i - ∏ i ∈ s, v i ^ α i ∈ scaledIdeal τ K c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    obtain ⟨z, hz, ez⟩ := pow_add_sub_pow hdp (v a) (u a - v a) (huv a) (α a)
    rw [add_sub_cancel] at ez
    have e : u a ^ α a * ∏ i ∈ s, u i ^ α i - v a ^ α a * ∏ i ∈ s, v i ^ α i =
        u a ^ α a * (∏ i ∈ s, u i ^ α i - ∏ i ∈ s, v i ^ α i) +
          (u a ^ α a - v a ^ α a) * ∏ i ∈ s, v i ^ α i := by ring
    rw [e, ez]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) (Ideal.mul_mem_right _ _ (hsc a z hz))

end GlobalTheory.KatzCongr

namespace GlobalTheory.KatzCongr

theorem subst_sub_in : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ τ : Type) [Fintype σ] (N : Ideal B) (f : MvPowerSeries σ Q) (u v : σ → MvPowerSeries τ B), DIn N f → (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i α, coeff α (u i - v i) ∈ J) → In (J * N) (subst (up Q u) f - subst (up Q v) f) := by
  intro p _ B O Q _ _ _ _ θ hF J hJ σ τ _ N f u v hf hu hv huv
  classical
  have hdp : ∀ w ∈ coeffIdeal τ J, ∀ n : ℕ, 0 < n →
      ∃ y ∈ coeffIdeal τ J, w ^ n = (n.factorial : MvPowerSeries τ B) * y := fun w hw n hn => by
    obtain ⟨y, hy, e⟩ := GlobalTheory.T.mvPowerSeries_coeffsInIdeal_pow_eq_factorial_mul p B O Q θ hF J hJ τ w hw n hn
    exact ⟨y, hy, e⟩
  have hsU : HasSubst (up Q u) := hasSubst_of_constantCoeff_zero fun i => by simp [up, hu i]
  have hsV : HasSubst (up Q v) := hasSubst_of_constantCoeff_zero fun i => by simp [up, hv i]
  intro γ
  rw [map_sub, coeff_subst hsU, coeff_subst hsV,
    ← finsum_sub_distrib (coeff_subst_finite hsU f γ) (coeff_subst_finite hsV f γ)]
  refine finsum_induction (fun q => ∃ b ∈ J * N, q = algebraMap B Q b) ⟨0, Submodule.zero_mem _, by simp⟩
    (fun x y ⟨a, ha, ea⟩ ⟨b, hb, eb⟩ => ⟨a + b, Submodule.add_mem _ ha hb, by rw [ea, eb, map_add]⟩)
    (fun d => ?_)
  have hprod : ∀ w : σ → MvPowerSeries τ B,
      (d.prod fun s e => up Q w s ^ e) = map (algebraMap B Q) (∏ i, w i ^ d i) := by
    intro w
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), map_prod]
    simp [up, map_pow]
  have hsc : ∀ i, ∀ z ∈ coeffIdeal τ J,
      (d i : MvPowerSeries τ B) * z ∈ scaledIdeal τ (J * N) (coeff d f) := by
    intro i z hz γ'
    obtain ⟨b, hb, eb⟩ := hf d i
    refine ⟨coeff γ' z * b, Ideal.mul_mem_mul (hz γ') hb, ?_⟩
    rw [show ((d i : ℕ) : MvPowerSeries τ B) = C (d i : B) from (map_natCast C _).symm, coeff_C_mul,
      map_mul, map_mul, ← eb, map_natCast]
    ring
  have hmem := prod_sub_mem (J := J) (J * N) (coeff d f) d u v hdp (fun i α => huv i α) hsc Finset.univ
  obtain ⟨b, hb, eb⟩ := hmem γ
  refine ⟨b, hb, ?_⟩
  rw [hprod, hprod, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub (coeff γ), ← map_sub, coeff_map, ← eb]

end GlobalTheory.KatzCongr
