import ReciprocityTheory.Chebotarev.CasimirPowerSurjectiveSymmetric
import ReciprocityTheory.Chebotarev.EulerSum

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem norm_neg_log_one_sub_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖-Complex.log (1 - z) - z‖ ≤ ‖z‖ ^ 2 := by
  have h1 : ‖-z‖ < 1 := by rw [norm_neg]; linarith
  have h := Complex.norm_log_one_add_sub_self_le h1
  rw [norm_neg] at h
  have e : -Complex.log (1 - z) - z = -(Complex.log (1 + -z) - -z) := by ring_nf
  rw [e, norm_neg]
  refine h.trans ?_
  have h0 : 0 ≤ ‖z‖ := norm_nonneg _
  have h2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  calc ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖z‖ ^ 2 := by ring

theorem psum_term_norm_le {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ)
    (q : Prm E) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  have hN : (0 : ℕ) < Nrm q := by have := two_le_Nrm q; omega
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN]
  simp only [Complex.neg_re, Complex.ofReal_re]
  have := DirichletCharacter.norm_le_one χ ((Nrm q : ℕ) : ZMod l)
  have hp : 0 ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := Real.rpow_nonneg (by positivity) _
  nlinarith

theorem Nrm_rpow_neg_le_inv {E : Type} [Field E] [NumberField E] {s : ℝ} (hs : 1 < s) (q : Prm E) :
    ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := by
  have h2 : (2 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
  rw [← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem casimirPower_surjective_symmetric' : CasimirPowerSurjectiveSymmetric := by
  intro E _ _ l _ χ
  refine ⟨∑' q : Prm E, ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)), fun s hs => ?_⟩
  set z : Prm E → ℂ := fun q => χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)) with hzdef
  have hzb : ∀ q, ‖z q‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := fun q => psum_term_norm_le χ s q
  have hzs : Summable z := Summable.of_norm_bounded (summable_prm_rpow E hs) hzb
  have hls : Summable (fun q => -Complex.log (1 - z q)) := hzs.clog_one_sub.neg
  have hsq : ∀ q, ‖-Complex.log (1 - z q) - z q‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
    intro q
    have h2 : (2 : ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
    have hz1 : ‖z q‖ ≤ ((Nrm q : ℕ) : ℝ)⁻¹ := (hzb q).trans (Nrm_rpow_neg_le_inv hs q)
    have hz2 : ‖z q‖ ≤ 1 / 2 := hz1.trans (by rw [one_div]; exact inv_anti₀ (by norm_num) h2)
    refine (norm_neg_log_one_sub_sub_le hz2).trans ?_
    rw [Real.rpow_neg (by linarith), Real.rpow_two, ← inv_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hz1 2
  have e : abelian₂ E χ s - Psum E χ s = ∑' q, (-Complex.log (1 - z q) - z q) := by
    unfold abelian₂ Psum
    exact (hls.tsum_sub hzs).symm
  rw [e]
  exact tsum_of_norm_bounded (summable_prm_rpow E (by norm_num : (1 : ℝ) < 2)).hasSum hsq

end ReciprocityTheory.Cheb
