import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepSingleSat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.DescentStep

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]

lemma kappa_real : conj (repKappa a b d ha hd lam hlam) = repKappa a b d ha hd lam hlam := by
  unfold repKappa
  simp only [map_mul, map_inv₀, Complex.conj_ofReal, map_natCast]

lemma not_dvd_mul' {l : ℕ} (hl : l.Prime) {u v : ℤ} (hu : ¬ (l : ℤ) ∣ u) (hv : ¬ (l : ℤ) ∣ v) :
    ¬ (l : ℤ) ∣ u * v := by
  intro h
  rcases (Nat.prime_iff_prime_int.mp hl).dvd_or_dvd h with h1 | h1
  · exact hu h1
  · exact hv h1

lemma H_nsmul_nsmul (L : PeriodPair) (s t : ℕ) (v w : m → ℂ) :
    stdH L m (s • v) (t • w) = (s : ℂ) * t * stdH L m v w := by
  simp only [stdH, matH, LinearMap.mk₂'ₛₗ_apply, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    simp only [Pi.mul_apply, Pi.natCast_apply, map_mul, map_natCast]
    ring

lemma H_self_ne (L : PeriodPair) {v : m → ℂ} (hv : v ≠ 0) : stdH L m v v ≠ 0 := by
  rw [stdH_apply]
  have hA : area L ≠ 0 := by rw [area_eq]; exact abs_ne_zero.mpr (detD_ne L)
  refine mul_ne_zero ?_ (inv_ne_zero (by exact_mod_cast hA))
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by by_contra h; push_neg at h; exact hv (funext h)
  have hsum : (∑ j, v j * conj (v j)) = ((∑ j, Complex.normSq (v j) : ℝ) : ℂ) := by
    push_cast; exact Finset.sum_congr rfl fun j _ => Complex.mul_conj (v j)
  rw [hsum]
  have : 0 < ∑ j, Complex.normSq (v j) :=
    Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  exact_mod_cast this.ne'

variable {a b c d ha hd lam hlam m}

lemma sat_norm (hOK : CmOK a b c d) {Λ : AddSubgroup (m → ℂ)}
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) {v : m → ℂ} (hv : SatMem l Λ v) :
    ∃ p q : ℤ, ¬ (l : ℤ) ∣ q ∧ stdH (cmL a b d ha hd lam hlam) m v v = repKappa a b d ha hd lam hlam * p / q := by
  obtain ⟨s, hs, hsv⟩ := hv
  obtain ⟨n, hn⟩ := rep_H_self_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hsv
  have hs' : ¬ (l : ℤ) ∣ (s : ℤ) := fun h => hs (by exact_mod_cast h)
  refine ⟨n, (s : ℤ) * s, not_dvd_mul' hl hs' hs', ?_⟩
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h; apply hs; rw [show s = 0 by exact_mod_cast h]; exact dvd_zero _
  rw [H_nsmul_nsmul] at hn
  push_cast
  field_simp
  linear_combination hn

lemma sat_pair (hOK : CmOK a b c d) {Λ : AddSubgroup (m → ℂ)}
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) {v w : m → ℂ} (hv : SatMem l Λ v) (hw : SatMem l Λ w) :
    ∃ n c₂ s : ℤ, ¬ (l : ℤ) ∣ s ∧ stdH (cmL a b d ha hd lam hlam) m v w =
      repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)) / s := by
  obtain ⟨s, hs, hsv⟩ := hv
  obtain ⟨t, ht, htw⟩ := hw
  obtain ⟨n, c₂, hn, -⟩ := rep_H_int a b c d ha hd lam hlam m hOK Λ hΛ hθ hsv htw
  have hs' : ¬ (l : ℤ) ∣ (s : ℤ) := fun h => hs (by exact_mod_cast h)
  have ht' : ¬ (l : ℤ) ∣ (t : ℤ) := fun h => ht (by exact_mod_cast h)
  refine ⟨n, c₂, (s : ℤ) * t, not_dvd_mul' hl hs' ht', ?_⟩
  have hs0 : (s : ℂ) ≠ 0 := by
    intro h; apply hs; rw [show s = 0 by exact_mod_cast h]; exact dvd_zero _
  have ht0 : (t : ℂ) ≠ 0 := by
    intro h; apply ht; rw [show t = 0 by exact_mod_cast h]; exact dvd_zero _
  rw [H_nsmul_nsmul] at hn
  push_cast
  field_simp
  linear_combination hn

lemma im_pi_inv (n c₂ : ℤ) :
    ((2 * cmTheta b d - b)⁻¹ * (repKappa a b d ha hd lam hlam * ((n : ℂ) - c₂ * conj (cmTheta b d)))).im =
      -((2 * n - c₂ * b : ℤ) : ℝ) / d := by
  rw [rep_kappa_eq]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs : Real.sqrt d ≠ 0 := (Real.sqrt_pos.2 hd').ne'
  have hsq : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt hd'.le
  have hpi : 2 * cmTheta b d - b = Complex.I * ((Real.sqrt d : ℝ) : ℂ) := by
    unfold cmTheta
    ring
  have hconj : conj (cmTheta b d) = ((b : ℂ) - Complex.I * ((Real.sqrt d : ℝ) : ℂ)) / 2 := by
    unfold cmTheta
    simp [map_div₀, Complex.conj_ofReal, map_ofNat]
    ring
  rw [hpi, hconj]
  simp [Complex.mul_im, Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq, Complex.div_re,
    Complex.div_im]
  field_simp
  rw [show (Real.sqrt d) ^ 2 = d by rw [sq]; exact hsq] at *
  ring

end PI.UnitaryGroupMassFormula.UnimodLocStd
