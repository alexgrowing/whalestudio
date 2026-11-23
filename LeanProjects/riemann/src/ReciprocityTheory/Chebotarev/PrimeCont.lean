import ReciprocityTheory.Chebotarev.CasimirPowerSurjectiveSymmetric
import ReciprocityTheory.Chebotarev.EulerSum

open NumberField Filter Topology

namespace ReciprocityTheory.Cheb

theorem norm_chiNrm_cpow_le {E : Type} [Field E] [NumberField E] {l : ℕ} (χ : DirichletCharacter ℂ l)
    (q : Prm E) (s : ℝ) :
    ‖χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ ≤ ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  have hN : 0 < Nrm q := lt_of_lt_of_le (by norm_num) (two_le_Nrm q)
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hN]
  have h1 := χ.norm_le_one ((Nrm q : ℕ) : ZMod l)
  have h2 : (0:ℝ) ≤ ((Nrm q : ℕ) : ℝ) ^ (-(s:ℂ)).re := Real.rpow_nonneg (by positivity) _
  simp only [Complex.neg_re, Complex.ofReal_re] at h2 ⊢
  nlinarith [norm_nonneg (χ ((Nrm q : ℕ) : ZMod l))]

theorem nrm_rpow_neg_le_half {E : Type} [Field E] [NumberField E] (q : Prm E) {s : ℝ} (hs : 1 ≤ s) :
    ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ 1 / 2 := by
  have h2 : (2:ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
  calc ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = (((Nrm q : ℕ) : ℝ))⁻¹ := Real.rpow_neg_one _
    _ ≤ 1 / 2 := by rw [one_div]; exact inv_anti₀ (by norm_num) h2

theorem smoothMap_seminorm_bound' : SmoothMapSeminormBound := by
  intro E _ _ l _ χ s0 hs0
  have hs0' : (1:ℝ) < s0 := hs0
  set a : ℝ := (1 + s0) / 2 with ha_def
  have ha1 : 1 < a := by rw [ha_def]; linarith
  have has0 : a < s0 := by rw [ha_def]; linarith
  have hcont : ContinuousOn (fun s : ℝ => abelian₂ E χ s) (Set.Ioi a) := by
    unfold abelian₂
    refine continuousOn_tsum (u := fun q : Prm E => (3 / 2) * ((Nrm q : ℕ) : ℝ) ^ (-a)) ?_
      ((summable_prm_rpow E ha1).mul_left _) ?_
    · intro q
      have hN : (Nrm q : ℕ) ≠ 0 := by have := two_le_Nrm q; omega
      have hc : Continuous (fun s : ℝ => χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))) :=
        continuous_const.mul (Continuous.const_cpow (Complex.continuous_ofReal.neg)
          (Or.inl (by exact_mod_cast hN)))
      refine ContinuousOn.neg (ContinuousOn.clog (continuous_const.sub hc).continuousOn ?_)
      intro s hs
      have hs' : a < s := hs
      have hz := (norm_chiNrm_cpow_le χ q s).trans (nrm_rpow_neg_le_half q (by linarith))
      rw [Complex.mem_slitPlane_iff]
      left
      have hre := Complex.abs_re_le_norm (χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)))
      rw [Complex.sub_re, Complex.one_re]
      have := (abs_le.mp (hre.trans hz)).2
      linarith
    · intro q s hs
      have hs' : a < s := hs
      have hz1 := norm_chiNrm_cpow_le χ q s
      have hz := hz1.trans (nrm_rpow_neg_le_half q (by linarith))
      rw [norm_neg, sub_eq_add_neg]
      have hz' : ‖-(χ ((Nrm q : ℕ) : ZMod l) * ((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ)))‖ ≤ 1 / 2 := by
        rw [norm_neg]; exact hz
      refine (Complex.norm_log_one_add_half_le_self hz').trans ?_
      rw [norm_neg]
      have hmono : ((Nrm q : ℕ) : ℝ) ^ (-s) ≤ ((Nrm q : ℕ) : ℝ) ^ (-a) := by
        have h2 : (2:ℝ) ≤ ((Nrm q : ℕ) : ℝ) := by exact_mod_cast two_le_Nrm q
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      nlinarith
  exact (hcont.continuousAt (Ioi_mem_nhds has0)).continuousWithinAt

end ReciprocityTheory.Cheb
