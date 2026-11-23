import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermZeroRight

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

theorem herm_zero_of_trace {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (u v : Fin (2 * r + k + 1) → ℂ)
    (h1 : (Matrix.trace (ζ * Xuv k r u v)).re = 0)
    (h2 : (Matrix.trace (ζ * Xuv k r u (Complex.I • v))).re = 0) :
    herm (Hpk k r) (ζ *ᵥ u) v = 0 := by
  rw [trace_xuv] at h1 h2
  have hs : ∀ w, herm (Hpk k r) (ζ *ᵥ w) u = -star (herm (Hpk k r) (ζ *ᵥ u) w) := by
    intro w
    rw [herm_skew hζ, herm_swap w]
  rw [hs] at h1 h2
  rw [herm_smul_right] at h2
  set A := herm (Hpk k r) (ζ *ᵥ u) v
  simp [Complex.ext_iff, Complex.mul_re, Complex.mul_im] at h1 h2 ⊢
  constructor <;> linarith

theorem herm_bvec (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    herm (Hpk k r) x (bvec i) = (Hpk k r *ᵥ x) i := by
  rw [herm_eq, Finset.sum_eq_single i]
  · simp [bvec]
  · intro j _ hj; simp [bvec, hj]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem herm_e (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) x (bvec (eI k r b)) = x (esI k r b) := by
  rw [herm_bvec, hpk_mulVec, if_pos (Or.inl (by simp [eI]))]
  rfl

theorem herm_es (x : Fin (2 * r + k + 1) → ℂ) (b : Fin r) :
    herm (Hpk k r) x (bvec (esI k r b)) = x (eI k r b) := by
  rw [herm_bvec, hpk_mulVec, if_pos (Or.inr (by simp [esI]; omega))]
  congr 1
  apply Fin.ext
  simp [eI, esI]
  omega

theorem herm_w (x : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) (h1 : r ≤ i.val) (h2 : i.val ≤ r + k) :
    herm (Hpk k r) x (bvec i) = if i.val = r + k then -x i else x i := by
  rw [herm_bvec, hpk_mulVec, if_neg (by omega)]

theorem inWb_sub {u v : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (hv : inWb k r v) : inWb k r (u - v) := by
  intro i hi; simp [hu i hi, hv i hi]

theorem inWb_smul (c : ℂ) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) : inWb k r (c • u) := by
  intro i hi; simp [hu i hi]

def sg (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

theorem hpk_mulVec_wb {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ u) i = sg (k := k) (r := r) i * u i := by
  rw [hpk_mulVec, sg]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, hu i h, hu ⟨2 * r + k - i.val, by omega⟩ (by simp; omega), mul_zero]
  · rw [if_neg h]
    split_ifs <;> ring

def KI (k r : ℕ) : Fin (2 * r + k + 1) := ⟨r + k, by omega⟩

theorem herm_wb {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) (y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) u y = ∑ i ∈ Finset.univ.erase (KI k r), star (y i) * u i - star (y (KI k r)) * u (KI k r) := by
  rw [herm_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (KI k r))]
  have hK : sg (k := k) (r := r) (KI k r) = -1 := by simp [sg, KI]
  rw [hpk_mulVec_wb hu, hK]
  have : ∀ i ∈ Finset.univ.erase (KI k r), star (y i) * (Hpk k r *ᵥ u) i = star (y i) * u i := by
    intro i hi
    rw [hpk_mulVec_wb hu]
    have : i.val ≠ r + k := fun e => (Finset.mem_erase.1 hi).1 (Fin.ext (by simp [KI, e]))
    simp [sg, this]
  rw [Finset.sum_congr rfl this]
  ring

theorem re_star_mul_self (a : ℂ) : (star a * a).re = ‖a‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem wb_definite {z w : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hw : inWb k r w) (hwz : herm (Hpk k r) w z = 0) (hww : (herm (Hpk k r) w w).re ≤ 0) : w = 0 := by
  set S := Finset.univ.erase (KI k r)
  set K := KI k r
  have e2 : (herm (Hpk k r) w w).re = ∑ i ∈ S, ‖w i‖ ^ 2 - ‖w K‖ ^ 2 := by
    rw [herm_wb hw, Complex.sub_re, Complex.re_sum, re_star_mul_self]
    simp only [re_star_mul_self]
    rfl
  have eT : Tz k r z = ‖z K‖ ^ 2 - ∑ i ∈ S, ‖z i‖ ^ 2 := by
    rw [Tz, herm_wb hz, Complex.sub_re, Complex.re_sum, re_star_mul_self]
    simp only [re_star_mul_self]
    ring
  rw [herm_wb hw, sub_eq_zero] at hwz
  have hn : ‖z K‖ * ‖w K‖ ≤ ∑ i ∈ S, ‖z i‖ * ‖w i‖ := by
    calc ‖z K‖ * ‖w K‖ = ‖star (z K) * w K‖ := by rw [norm_mul, norm_star]
      _ = ‖∑ i ∈ S, star (z i) * w i‖ := by rw [hwz]
      _ ≤ ∑ i ∈ S, ‖star (z i) * w i‖ := norm_sum_le _ _
      _ = ∑ i ∈ S, ‖z i‖ * ‖w i‖ := by simp only [norm_mul, norm_star]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun i => ‖z i‖) (fun i => ‖w i‖)
  set P := ∑ i ∈ S, ‖w i‖ ^ 2
  set Q := ∑ i ∈ S, ‖z i‖ ^ 2
  set m := ∑ i ∈ S, ‖z i‖ * ‖w i‖
  have hP : 0 ≤ P := Finset.sum_nonneg (fun i _ => by positivity)
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => by positivity)
  have ha : 0 ≤ ‖w K‖ := norm_nonneg _
  have hc : 0 ≤ ‖z K‖ := norm_nonneg _
  have h1 : P ≤ ‖w K‖ ^ 2 := by linarith
  have h2 : Q < ‖z K‖ ^ 2 := by linarith
  have h3 : (‖z K‖ * ‖w K‖) ^ 2 ≤ m ^ 2 := by
    have : 0 ≤ ‖z K‖ * ‖w K‖ := by positivity
    exact pow_le_pow_left₀ this hn 2
  have h4 : (‖z K‖ * ‖w K‖) ^ 2 ≤ Q * ‖w K‖ ^ 2 := by
    calc (‖z K‖ * ‖w K‖) ^ 2 ≤ m ^ 2 := h3
      _ ≤ Q * P := hcs
      _ ≤ Q * ‖w K‖ ^ 2 := mul_le_mul_of_nonneg_left h1 hQ
  have h5 : ‖w K‖ ^ 2 * (‖z K‖ ^ 2 - Q) ≤ 0 := by nlinarith
  have h6 : ‖w K‖ ^ 2 ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have : 0 < ‖w K‖ ^ 2 * (‖z K‖ ^ 2 - Q) := mul_pos hcon (by linarith)
    linarith
  have hwK : w K = 0 := by
    have : ‖w K‖ = 0 := by nlinarith
    exact norm_eq_zero.1 this
  have hP0 : P = 0 := le_antisymm (by nlinarith) hP
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hP0
  funext i
  by_cases hi : i = K
  · rw [hi, hwK]; rfl
  · have := hall i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, norm_eq_zero] at this
    rw [this]; rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
