import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section
namespace GlobalTheory.MomOne.Shift
variable {q : ℕ} [Fact q.Prime]

def sS (ζ : ℂ_[q]) : ℂ_[q]⟦X⟧ := C ζ * (1 + X) - 1

lemma coeff_sS_pow (ζ : ℂ_[q]) (m n : ℕ) :
    coeff n (sS ζ ^ m) = (m.choose n : ℂ_[q]) * ζ ^ n * (ζ - 1) ^ (m - n) := by
  have hs : sS ζ = C ζ * X + C (ζ - 1) := by
    simp only [sS, map_sub, map_one]
    ring
  have hterm : ∀ k ∈ Finset.range (m + 1),
      (C ζ * X) ^ k * C (ζ - 1) ^ (m - k) * (m.choose k : ℂ_[q]⟦X⟧) =
        C (ζ ^ k * (ζ - 1) ^ (m - k) * (m.choose k : ℂ_[q])) * X ^ k := by
    intro k _
    simp only [mul_pow, map_mul, map_pow, map_natCast]
    ring
  rw [hs, add_pow, Finset.sum_congr rfl hterm, map_sum]
  simp only [PowerSeries.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hn
  · ring
  · rw [Finset.mem_range] at hn
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

lemma coeff_shiftS (ζ : ℂ_[q]) (f : ℂ_[q]⟦X⟧) (n : ℕ) :
    coeff n (shiftS ζ f) = ∑' m, coeff m f * coeff n (sS ζ ^ m) := by
  simp only [shiftS, PowerSeries.coeff_mk, coeff_sS_pow]

lemma norm_le_one_of {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) : ‖ζ‖ ≤ 1 := by
  calc ‖ζ‖ = ‖(ζ - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ max ‖ζ - 1‖ ‖(1 : ℂ_[q])‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le h.le (by rw [norm_one])

lemma norm_coeff_sS_pow {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) (m n : ℕ) :
    ‖coeff n (sS ζ ^ m)‖ ≤ ‖ζ - 1‖ ^ (m - n) := by
  rw [coeff_sS_pow, norm_mul, norm_mul, norm_pow, norm_pow]
  have h1 := IsUltrametricDist.norm_natCast_le_one ℂ_[q] (m.choose n)
  have h2 : ‖ζ‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg _) (norm_le_one_of h)
  calc ‖(m.choose n : ℂ_[q])‖ * ‖ζ‖ ^ n * ‖ζ - 1‖ ^ (m - n) ≤ 1 * 1 * ‖ζ - 1‖ ^ (m - n) := by gcongr
    _ = ‖ζ - 1‖ ^ (m - n) := by ring

lemma summable_norm_term {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {a : ℕ → ℂ_[q]} {B : ℝ} (ha : ∀ m, ‖a m‖ ≤ B)
    (n : ℕ) : Summable fun m => ‖a m * coeff n (sS ζ ^ m)‖ := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (ha 0)
  have hg : Summable fun m : ℕ => B * ‖ζ - 1‖ ^ (m - n) := by
    refine Summable.mul_left B ((summable_nat_add_iff n).mp ?_)
    simpa using summable_geometric_of_lt_one (norm_nonneg (ζ - 1)) h
  refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_) hg
  rw [norm_mul]
  exact mul_le_mul (ha m) (norm_coeff_sS_pow h m n) (norm_nonneg _) hB0

lemma summable_term {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {a : ℕ → ℂ_[q]} {B : ℝ} (ha : ∀ m, ‖a m‖ ≤ B)
    (n : ℕ) : Summable fun m => a m * coeff n (sS ζ ^ m) := (summable_norm_term h ha n).of_norm

lemma bd_shiftS {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {f : ℂ_[q]⟦X⟧} {B : ℝ} (hf : Bd B f) :
    Bd B (shiftS ζ f) := by
  intro n
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hf 0)
  rw [coeff_shiftS]
  have hs := summable_term (a := fun m => coeff m f) h hf n
  have hterm : ∀ m, ‖coeff m f * coeff n (sS ζ ^ m)‖ ≤ B := fun m => by
    rw [norm_mul]
    calc ‖coeff m f‖ * ‖coeff n (sS ζ ^ m)‖ ≤ B * 1 :=
          mul_le_mul (hf m) ((norm_coeff_sS_pow h m n).trans (pow_le_one₀ (norm_nonneg _) h.le))
            (norm_nonneg _) hB0
      _ = B := mul_one B
  have hcl : IsClosed {x : ℂ_[q] | ‖x‖ ≤ B} := isClosed_le continuous_norm continuous_const
  refine hcl.mem_of_tendsto hs.hasSum.tendsto_sum_nat (Filter.Eventually.of_forall fun N => ?_)
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun m _ => hterm m

lemma shiftS_add {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) :
    shiftS ζ (f + g) = shiftS ζ f + shiftS ζ g := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨B', hB'⟩ := hg
  ext n
  rw [map_add, coeff_shiftS, coeff_shiftS, coeff_shiftS]
  simp only [map_add, add_mul]
  exact (summable_term (a := fun m => coeff m f) h hB n).tsum_add
    (summable_term (a := fun m => coeff m g) h hB' n)

lemma shiftS_mul {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) :
    shiftS ζ (f * g) = shiftS ζ f * shiftS ζ g := by
  obtain ⟨B, hB⟩ := hf
  obtain ⟨B', hB'⟩ := hg
  ext n
  simp only [coeff_shiftS, PowerSeries.coeff_mul]
  have hprod : ∀ p : ℕ × ℕ, (∑' m, coeff m f * coeff p.1 (sS ζ ^ m)) * (∑' m, coeff m g * coeff p.2 (sS ζ ^ m)) =
      ∑' m, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
        (coeff x.1 f * coeff p.1 (sS ζ ^ x.1)) * (coeff x.2 g * coeff p.2 (sS ζ ^ x.2)) := fun p =>
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
      (summable_norm_term (a := fun m => coeff m f) h hB p.1)
      (summable_norm_term (a := fun m => coeff m g) h hB' p.2)
  have hsum : ∀ p : ℕ × ℕ, Summable fun m => ∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
      (coeff x.1 f * coeff p.1 (sS ζ ^ x.1)) * (coeff x.2 g * coeff p.2 (sS ζ ^ x.2)) := fun p =>
    (summable_norm_sum_mul_antidiagonal_of_summable_norm
      (summable_norm_term (a := fun m => coeff m f) h hB p.1)
      (summable_norm_term (a := fun m => coeff m g) h hB' p.2)).of_norm
  rw [Finset.sum_congr rfl (fun p _ => hprod p), ← Summable.tsum_finsetSum (fun p _ => hsum p)]
  refine tsum_congr fun m => ?_
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [← hx', pow_add, PowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

lemma shiftS_C (ζ c : ℂ_[q]) : shiftS ζ (C c) = C c := by
  ext n
  rw [coeff_shiftS, tsum_eq_single 0 (fun m hm => by simp [PowerSeries.coeff_C, hm])]
  by_cases hn : n = 0 <;> simp [PowerSeries.coeff_C, PowerSeries.coeff_one, hn]

lemma shiftS_X (ζ : ℂ_[q]) : shiftS ζ X = C ζ * (1 + X) - 1 := by
  ext n
  rw [coeff_shiftS, tsum_eq_single 1 (fun m hm => by simp [PowerSeries.coeff_X, hm])]
  simp [sS]

lemma constantCoeff_shiftS (ζ : ℂ_[q]) (f : ℂ_[q]⟦X⟧) :
    constantCoeff (shiftS ζ f) = ev f (ζ - 1) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_shiftS]
  simp [coeff_sS_pow, ev]

lemma shiftS_one (f : ℂ_[q]⟦X⟧) : shiftS 1 f = f := by
  ext n
  rw [coeff_shiftS, tsum_eq_single n (fun m hm => ?_)]
  · simp [coeff_sS_pow]
  · rw [coeff_sS_pow]
    rcases lt_or_gt_of_ne hm with hlt | hlt
    · simp [Nat.choose_eq_zero_of_lt hlt]
    · simp [Nat.sub_ne_zero_of_lt hlt]

lemma coeff_DT (f : ℂ_[q]⟦X⟧) (n : ℕ) :
    coeff n (DT f) = coeff (n + 1) f * ((n : ℂ_[q]) + 1) + coeff n f * n := by
  rcases n with _ | n
  · rw [DT, add_mul, one_mul, map_add, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_derivative]
    simp
  · simp [DT, add_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_succ_X_mul]

lemma DT_sS_pow (ζ : ℂ_[q]) (m : ℕ) :
    DT (sS ζ ^ m) = C (m : ℂ_[q]) * (sS ζ ^ (m - 1) + sS ζ ^ m) := by
  unfold DT
  rw [Derivation.leibniz_pow]
  have hd : derivative ℂ_[q] (sS ζ) = C ζ := by simp [sS]
  have h1 : (1 + X) * C ζ = sS ζ + 1 := by
    unfold sS
    ring
  rw [hd]
  rcases m with _ | m
  · simp
  · simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul, map_natCast]
    rw [show (1 + X) * ((((m + 1 : ℕ) : ℂ_[q]⟦X⟧)) * (sS ζ ^ m * C ζ)) =
        ((m + 1 : ℕ) : ℂ_[q]⟦X⟧) * sS ζ ^ m * ((1 + X) * C ζ) by ring, h1, pow_succ]
    ring

lemma DT_shiftS {ζ : ℂ_[q]} (h : ‖ζ - 1‖ < 1) {f : ℂ_[q]⟦X⟧} (hf : Bdd f) :
    DT (shiftS ζ f) = shiftS ζ (DT f) := by
  obtain ⟨B, hB⟩ := hf
  have hn1 : ∀ m : ℕ, ‖(m : ℂ_[q])‖ ≤ 1 := fun m => IsUltrametricDist.norm_natCast_le_one ℂ_[q] m
  have hB1 : ∀ m : ℕ, ‖coeff m f * (m : ℂ_[q])‖ ≤ B := fun m => by
    rw [norm_mul]
    nlinarith [hB m, hn1 m, norm_nonneg (coeff m f), norm_nonneg (m : ℂ_[q])]
  have hB2 : ∀ m : ℕ, ‖coeff (m + 1) f * ((m : ℂ_[q]) + 1)‖ ≤ B := fun m => by
    have h0 := hB1 (m + 1)
    push_cast at h0
    exact h0
  ext n
  have hk : ∀ m : ℕ, coeff (n + 1) (sS ζ ^ m) * ((n : ℂ_[q]) + 1) + coeff n (sS ζ ^ m) * n =
      (m : ℂ_[q]) * coeff n (sS ζ ^ (m - 1)) + (m : ℂ_[q]) * coeff n (sS ζ ^ m) := by
    intro m
    rw [← coeff_DT, DT_sS_pow, PowerSeries.coeff_C_mul, map_add, mul_add]
  have s0 := summable_term (a := fun m => coeff m f) h hB n
  have s1 := summable_term (a := fun m => coeff m f) h hB (n + 1)
  have s2 := summable_term (a := fun m => coeff m f * (m : ℂ_[q])) h hB1 n
  have s3 := summable_term (a := fun m => coeff (m + 1) f * ((m : ℂ_[q]) + 1)) h hB2 n
  have s4 : Summable fun m : ℕ => coeff m f * (m : ℂ_[q]) * coeff n (sS ζ ^ (m - 1)) := by
    refine (summable_nat_add_iff 1).mp ?_
    simpa using s3
  rw [coeff_DT, coeff_shiftS, coeff_shiftS, coeff_shiftS]
  simp only [coeff_DT, add_mul]
  calc (∑' m, coeff m f * coeff (n + 1) (sS ζ ^ m)) * ((n : ℂ_[q]) + 1) +
        (∑' m, coeff m f * coeff n (sS ζ ^ m)) * n
      = ∑' m, (coeff m f * coeff (n + 1) (sS ζ ^ m) * ((n : ℂ_[q]) + 1) +
          coeff m f * coeff n (sS ζ ^ m) * n) := by
        rw [← tsum_mul_right, ← tsum_mul_right, ← Summable.tsum_add (s1.mul_right _) (s0.mul_right _)]
    _ = ∑' m, (coeff m f * (m : ℂ_[q]) * coeff n (sS ζ ^ (m - 1)) +
          coeff m f * (m : ℂ_[q]) * coeff n (sS ζ ^ m)) :=
        tsum_congr fun m => by linear_combination (coeff m f) * hk m
    _ = ∑' m, coeff m f * (m : ℂ_[q]) * coeff n (sS ζ ^ (m - 1)) +
          ∑' m, coeff m f * (m : ℂ_[q]) * coeff n (sS ζ ^ m) := s4.tsum_add s2
    _ = ∑' m, coeff (m + 1) f * ((m : ℂ_[q]) + 1) * coeff n (sS ζ ^ m) +
          ∑' m, coeff m f * (m : ℂ_[q]) * coeff n (sS ζ ^ m) := by
        rw [s4.tsum_eq_zero_add]
        simp
    _ = _ := (s3.tsum_add s2).symm

theorem shift_laws : ∀ (q : ℕ) [Fact q.Prime] (ζ : ℂ_[q]), ‖ζ - 1‖ < 1 → (∀ (f : ℂ_[q]⟦X⟧) (B : ℝ), Bd B f → Bd B (shiftS ζ f)) ∧ (∀ f g : ℂ_[q]⟦X⟧, Bdd f → Bdd g → shiftS ζ (f + g) = shiftS ζ f + shiftS ζ g ∧ shiftS ζ (f * g) = shiftS ζ f * shiftS ζ g) ∧ (∀ c : ℂ_[q], shiftS ζ (C c) = C c) ∧ shiftS ζ X = C ζ * (1 + X) - 1 ∧ (∀ f : ℂ_[q]⟦X⟧, constantCoeff (shiftS ζ f) = ev f (ζ - 1)) ∧ (∀ f : ℂ_[q]⟦X⟧, Bdd f → DT (shiftS ζ f) = shiftS ζ (DT f)) ∧ (∀ f : ℂ_[q]⟦X⟧, shiftS 1 f = f) := by
  intro q _ ζ h
  exact ⟨fun f B hf => bd_shiftS h hf, fun f g hf hg => ⟨shiftS_add h hf hg, shiftS_mul h hf hg⟩,
    shiftS_C ζ, shiftS_X ζ, constantCoeff_shiftS ζ, fun f hf => DT_shiftS h hf, shiftS_one⟩

end GlobalTheory.MomOne.Shift
