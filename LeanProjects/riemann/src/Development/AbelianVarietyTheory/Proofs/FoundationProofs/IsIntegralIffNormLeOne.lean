import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotZeroChi
open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

noncomputable section

namespace GlobalTheory.KZ.AutoPin

variable {l : ℕ} [Fact l.Prime]

def compPow (l : ℕ) [Fact l.Prime] (B : PowerSeries (Qbar l)) : PowerSeries (Qbar l) :=
  PowerSeries.mk fun n =>
    ∑ k ∈ Finset.range (n + 1), B.coeff k * ((((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l))) ^ k).coeff n

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h, Padic.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)

theorem norm_l_pos : 0 < ‖((l : ℕ) : Qbar l)‖ := by
  have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [map_natCast] at h
  rw [h, Padic.norm_p]
  exact inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)

theorem norm_lpow_anti {k n : ℕ} (h : k ≤ n) : ‖((l : ℕ) : Qbar l) ^ n‖ ≤ ‖((l : ℕ) : Qbar l) ^ k‖ := by
  rw [norm_pow, norm_pow]
  exact pow_le_pow_of_le_one (norm_nonneg _) norm_l_lt_one.le h

theorem cg_trans {n : ℕ} {a b d : Qbar l} (h1 : Cg n a b) (h2 : Cg n b d) : Cg n a d := by
  unfold Cg at *
  calc ‖a - d‖ = ‖(a - b) + (b - d)‖ := by ring_nf
    _ ≤ max ‖a - b‖ ‖b - d‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ _ := max_le h1 h2

theorem cg_symm {n : ℕ} {a b : Qbar l} (h : Cg n a b) : Cg n b a := by
  unfold Cg at *; rwa [norm_sub_rev]

theorem cg_mono {k n : ℕ} {a b : Qbar l} (h : Cg n a b) (hk : k ≤ n) : Cg k a b :=
  le_trans h (norm_lpow_anti hk)

theorem cg_mul {n : ℕ} {x a b : Qbar l} (hx : ‖x‖ ≤ 1) (h : Cg n a b) : Cg n (x * a) (x * b) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  exact le_trans (mul_le_of_le_one_left (norm_nonneg _) hx) h

theorem norm_tval_le (B : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) (hB : ∀ n, ‖B.coeff n‖ ≤ 1) (hz : ‖z - 1‖ ≤ 1) :
    ‖tval B N z‖ ≤ 1 := by
  unfold tval
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun n _ => ?_
  rw [norm_mul, norm_pow]
  exact mul_le_one₀ (hB n) (by positivity) (pow_le_one₀ (norm_nonneg _) hz)

theorem tval_sub (P Q : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) : tval (P - Q) N z = tval P N z - tval Q N z := by
  unfold tval; rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun n _ => ?_; simp [sub_mul]

theorem tval_smul (x : Qbar l) (P : PowerSeries (Qbar l)) (N : ℕ) (z : Qbar l) : tval (x • P) N z = x * tval P N z := by
  unfold tval; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun n _ => ?_; simp [mul_assoc]

theorem isIntegral_iff_norm_le_one (x : Qbar l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  (isIntegral_iff_norm_le_one x).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem intCast_mem (c : Coef l) (n : ℤ) : ((n : ℤ) : Qbar l) ∈ c.O := by
  have : ((n : ℤ) : Qbar l) = algebraMap ℤ_[l] (Qbar l) (n : ℤ_[l]) := by simp
  rw [this]; exact c.O.algebraMap_mem _

theorem polyPow_coeff_int (k n : ℕ) : ∃ t : ℤ,
    ((((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l))) ^ k).coeff n = (t : Qbar l) := by
  refine ⟨((((Polynomial.X + 1) ^ l - 1 : Polynomial ℤ)) ^ k).coeff n, ?_⟩
  have : (((Polynomial.X + 1) ^ l - 1 : Polynomial (Qbar l))) ^ k =
      Polynomial.map (Int.castRingHom (Qbar l)) ((((Polynomial.X + 1) ^ l - 1 : Polynomial ℤ)) ^ k) := by
    simp [Polynomial.map_pow, Polynomial.map_sub]
  rw [this, Polynomial.coeff_map]; rfl

theorem compPow_coeff_mem (c : Coef l) (B : PowerSeries (Qbar l)) (hB : ∀ n, B.coeff n ∈ c.O) (n : ℕ) :
    (compPow l B).coeff n ∈ c.O := by
  unfold compPow
  rw [PowerSeries.coeff_mk]
  refine sum_mem fun k _ => mul_mem (hB k) ?_
  obtain ⟨t, ht⟩ := polyPow_coeff_int (l := l) k n
  rw [ht]; exact intCast_mem c t

end GlobalTheory.KZ.AutoPin
