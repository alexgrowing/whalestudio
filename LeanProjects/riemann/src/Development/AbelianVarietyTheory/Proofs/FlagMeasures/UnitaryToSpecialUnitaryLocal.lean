import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SUSplit

variable {n : ℕ}

lemma det_Jm_ne_zero (ε : Fin n → Bool) : (Jm ε).det ≠ 0 := by
  have h := congrArg Matrix.det (Jm_mul_self ε)
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro h0
  rw [h0, zero_mul] at h
  exact zero_ne_one h

lemma norm_eq_one_of_pow {c : ℂ} (hn : n ≠ 0) (h : ‖c ^ n‖ = 1) : ‖c‖ = 1 := by
  rw [norm_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) hn).1 h

lemma star_mul_self_of_norm {c : ℂ} (hc : ‖c‖ = 1) : star c * c = 1 := by
  have h := Complex.normSq_eq_conj_mul_self (z := c)
  rw [Complex.normSq_eq_norm_sq, hc] at h
  simpa using h.symm

lemma norm_det_of_mem {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ‖g.det‖ = 1 := by
  have h : gᴴ * Jm ε * g = Jm ε := hg
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h2
  have h3 : star g.det * g.det = 1 := by
    have : (star g.det * g.det) * (Jm ε).det = 1 * (Jm ε).det := by rw [one_mul]; linear_combination h2
    exact mul_right_cancel₀ (det_Jm_ne_zero ε) this
  have h4 := Complex.normSq_eq_conj_mul_self (z := g.det)
  rw [Complex.normSq_eq_norm_sq] at h4
  have h5 : ‖g.det‖ ^ 2 = 1 := by
    have : ((‖g.det‖ ^ 2 : ℝ) : ℂ) = 1 := by rw [h4]; simpa using h3
    exact_mod_cast this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h5

lemma smul_mem_UJset_iff {ε : Fin n → Bool} {x : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hc : ‖c‖ = 1) :
    c • x ∈ UJset ε ↔ x ∈ UJset ε := by
  have hcc := star_mul_self_of_norm hc
  show inUJ ε (c • x) ↔ inUJ ε x
  unfold inUJ
  have : (c • x)ᴴ * Jm ε * (c • x) = (star c * c) • (xᴴ * Jm ε * x) := by
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [this, hcc, one_smul]

lemma smul_mem_Kset_iff {ε : Fin n → Bool} {x : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hc : ‖c‖ = 1) :
    c • x ∈ Kset ε ↔ x ∈ Kset ε := by
  have hcc := star_mul_self_of_norm hc
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  show (c • x ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ c • x * Jm ε = Jm ε * (c • x)) ↔
    (x ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ x * Jm ε = Jm ε * x)
  rw [Matrix.mem_unitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  have e1 : c • x * star (c • x) = (c * star c) • (x * star x) := by
    rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have e2 : c • x * Jm ε = c • (x * Jm ε) := Matrix.smul_mul _ _ _
  have e3 : Jm ε * (c • x) = c • (Jm ε * x) := Matrix.mul_smul _ _ _
  rw [e1, e2, e3, mul_comm, hcc, one_smul, smul_right_inj hc0]

lemma inv_smul_mem_SUset {ε : Fin n → Bool} {x : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (hx : x ∈ UJset ε)
    (hc : ‖c‖ = 1) (hpow : c ^ n = x.det) : c⁻¹ • x ∈ SUset ε := by
  have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
  refine ⟨(smul_mem_UJset_iff (by rw [norm_inv, hc, inv_one])).2 hx, ?_⟩
  rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hpow]
  exact inv_mul_cancel₀ (by rw [← hpow]; exact pow_ne_zero _ hc0)

theorem unit_scalar_split : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool), (∀ g ∈ UJset ε, ∃ z : ℂ, ‖z‖ = 1 ∧ ∃ g₀ ∈ SUset ε, g = z • g₀ ∧ (g ∈ Kset ε ↔ g₀ ∈ KS ε)) ∧ (∀ z : ℂ, ‖z‖ = 1 → ∀ g₀ ∈ SUset ε, z • g₀ ∈ UJset ε ∧ (g₀ ∈ KS ε → z • g₀ ∈ Kset ε)) ∧ ∀ g ∈ UJset ε, ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (ζ : Matrix (Fin n) (Fin n) ℂ → ℂ), IsOpen U ∧ g ∈ U ∧ ContinuousOn ζ U ∧ ∀ x ∈ U, x ∈ UJset ε → ‖ζ x‖ = 1 ∧ (ζ x)⁻¹ • x ∈ SUset ε := by
  intro n hn ε
  have hn0 : n ≠ 0 := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq g.det (by omega : 0 < n)
    have hzn : ‖z‖ = 1 := norm_eq_one_of_pow hn0 (by rw [hz]; exact norm_det_of_mem hg)
    have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hzn; exact zero_ne_one hzn
    have hmem := inv_smul_mem_SUset hg hzn hz
    refine ⟨z, hzn, z⁻¹ • g, hmem, ?_, ?_⟩
    · rw [smul_smul, mul_inv_cancel₀ hz0, one_smul]
    · have hzi : ‖z⁻¹‖ = 1 := by rw [norm_inv, hzn, inv_one]
      show g ∈ Kset ε ↔ (z⁻¹ • g ∈ Kset ε ∧ (z⁻¹ • g).det = 1)
      rw [smul_mem_Kset_iff hzi]
      exact ⟨fun h => ⟨h, hmem.2⟩, fun h => h.1⟩
  · intro z hz g₀ hg₀
    exact ⟨(smul_mem_UJset_iff hz).2 hg₀.1, fun h => (smul_mem_Kset_iff hz).2 h.1⟩
  · intro g hg
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq g.det (by omega : 0 < n)
    have hdg : g.det ≠ 0 := by
      intro h; have := norm_det_of_mem hg; rw [h, norm_zero] at this; exact zero_ne_one this
    have hcont : Continuous fun x : Matrix (Fin n) (Fin n) ℂ => x.det / g.det :=
      (continuous_id.matrix_det).div_const _
    refine ⟨{x | 0 < (x.det / g.det).re},
      fun x => z * Complex.exp (Complex.log (x.det / g.det) / n), ?_, ?_, ?_, ?_⟩
    · exact isOpen_lt continuous_const (Complex.continuous_re.comp hcont)
    · show 0 < (g.det / g.det).re
      rw [div_self hdg]; simp
    · refine continuousOn_const.mul (Complex.continuous_exp.comp_continuousOn ?_)
      exact (ContinuousOn.clog hcont.continuousOn
        (fun x hx => Complex.mem_slitPlane_iff.2 (Or.inl hx))).div_const _
    · intro x hxU hx
      have hw0 : x.det / g.det ≠ 0 := by
        intro h; have hxU' : 0 < (x.det / g.det).re := hxU; rw [h] at hxU'; simp at hxU'
      have hpow : (z * Complex.exp (Complex.log (x.det / g.det) / n)) ^ n = x.det := by
        rw [mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn0 : (n : ℂ) ≠ 0),
          Complex.exp_log hw0, hz, mul_div_cancel₀ _ hdg]
      have hnorm : ‖z * Complex.exp (Complex.log (x.det / g.det) / n)‖ = 1 :=
        norm_eq_one_of_pow hn0 (by rw [hpow]; exact norm_det_of_mem hx)
      exact ⟨hnorm, inv_smul_mem_SUset hx hnorm hpow⟩

end GlobalTheory.SUSplit

end
