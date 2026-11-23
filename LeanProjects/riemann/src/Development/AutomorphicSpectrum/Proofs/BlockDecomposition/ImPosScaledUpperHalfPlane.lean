import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
open Ad3 Ad3.S

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfTheta

open Complex
open scoped Real

theorem sqrt_scale {m : ℕ} (hm : 0 < m) {w : ℂ} (hw : w ≠ 0) :
    ((((m : ℝ) ^ 2 : ℝ) : ℂ) * w) ^ (1 / 2 : ℂ) = (m : ℂ) * w ^ (1 / 2 : ℂ) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hne : (((m : ℝ) ^ 2 : ℝ) : ℂ) * w ≠ 0 := mul_ne_zero (by exact_mod_cast hm2.ne') hw
  have hmc : (m : ℂ) = exp ((Real.log m : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hm']; simp
  rw [cpow_def_of_ne_zero hne, cpow_def_of_ne_zero hw, Complex.log_ofReal_mul hm2 hw, Real.log_pow, hmc,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_class (x : ℕ) (j : ℤ) (m : ℕ) (τ : ℂ) :
    ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ) =
      ee ((x : ℂ) ^ 2 * τ) * jacobiTheta₂_term j (2 * m * x * τ) (2 * m ^ 2 * τ) := by
  unfold ee jacobiTheta₂_term
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem im_pos_scaled_upper_half_plane {m : ℕ} (hm : 0 < m) {τ : ℂ} (hτ : 0 < τ.im) : 0 < (2 * (m : ℂ) ^ 2 * τ).im := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have : (2 * (m : ℂ) ^ 2 * τ) = (((2 * (m : ℝ) ^ 2 : ℝ)) : ℂ) * τ := by push_cast; ring
  rw [this, Complex.im_ofReal_mul]
  positivity

theorem prefactor {m : ℕ} (hm : 0 < m) {τ : ℂ} (hτ : 0 < τ.im) (x : ℕ) :
    ee ((x : ℂ) ^ 2 * τ) * (1 / (-I * (2 * (m : ℂ) ^ 2 * τ)) ^ (1 / 2 : ℂ) *
        cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ))) =
      (-2 * I * τ) ^ (-(1 / 2 : ℂ)) * (m : ℂ)⁻¹ := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hw : (-2 * I * τ) ≠ 0 := by simp [hτ0]
  have e1 : ee ((x : ℂ) ^ 2 * τ) * cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ)) = 1 := by
    unfold ee
    rw [← Complex.exp_add, Complex.exp_eq_one_iff]
    refine ⟨0, ?_⟩
    field_simp
    ring
  have e2 : (-I * (2 * (m : ℂ) ^ 2 * τ)) = (((m : ℝ) ^ 2 : ℝ) : ℂ) * (-2 * I * τ) := by
    push_cast; ring
  rw [e2, sqrt_scale hm hw, cpow_neg]
  have : ee ((x : ℂ) ^ 2 * τ) * (1 / ((m : ℂ) * (-2 * I * τ) ^ (1 / 2 : ℂ)) *
        cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ))) =
      (ee ((x : ℂ) ^ 2 * τ) * cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ))) *
        (1 / ((m : ℂ) * (-2 * I * τ) ^ (1 / 2 : ℂ))) := by ring
  rw [this, e1, one_mul, one_div, mul_inv, mul_comm]

theorem class_zero {m : ℕ} (hm : 0 < m) {τ : ℂ} (hτ : 0 < τ.im) (x : ℕ) :
    HasSum (fun j : ℤ => ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ))
      ((-2 * I * τ) ^ (-(1 / 2 : ℂ)) * (m : ℂ)⁻¹ * jacobiTheta₂ (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ))) := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have h := (hasSum_jacobiTheta₂_term (2 * m * x * τ) (im_pos_scaled_upper_half_plane hm hτ)).mul_left (ee ((x : ℂ) ^ 2 * τ))
  have hz : (2 * (m : ℂ) * x * τ) / (2 * (m : ℂ) ^ 2 * τ) = x / m := by field_simp
  rw [jacobiTheta₂_functional_equation, hz] at h
  have hf : (fun j : ℤ => ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ)) =
      fun i : ℤ => ee ((x : ℂ) ^ 2 * τ) * jacobiTheta₂_term i (2 * m * x * τ) (2 * m ^ 2 * τ) :=
    funext fun j => ee_class x j m τ
  rw [hf, ← prefactor hm hτ x]
  have hv : ee ((x : ℂ) ^ 2 * τ) * (1 / (-I * (2 * (m : ℂ) ^ 2 * τ)) ^ (1 / 2 : ℂ) *
        cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ))) *
        jacobiTheta₂ (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) =
      ee ((x : ℂ) ^ 2 * τ) * (1 / (-I * (2 * (m : ℂ) ^ 2 * τ)) ^ (1 / 2 : ℂ) *
        cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ)) *
        jacobiTheta₂ (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ))) := by ring
  rw [hv]
  exact h

theorem class_one {m : ℕ} (hm : 0 < m) {τ : ℂ} (hτ : 0 < τ.im) (x : ℕ) :
    HasSum (fun j : ℤ => (((x : ℤ) + m * j : ℤ) : ℂ) * ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ))
      ((-2 * I * τ) ^ (-(1 / 2 : ℂ)) * (2 * τ * m)⁻¹ * (m : ℂ)⁻¹ *
        (jacobiTheta₂' (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) / (2 * π * I))) := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpi : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
  have h0 := hasSum_jacobiTheta₂_term (2 * m * x * τ) (im_pos_scaled_upper_half_plane hm hτ)
  have h1 := hasSum_jacobiTheta₂'_term (2 * m * x * τ) (im_pos_scaled_upper_half_plane hm hτ)
  have h := ((h0.mul_left (x : ℂ)).add (h1.mul_left ((m : ℂ) / (2 * π * I)))).mul_left (ee ((x : ℂ) ^ 2 * τ))
  have hz : (2 * (m : ℂ) * x * τ) / (2 * (m : ℂ) ^ 2 * τ) = x / m := by field_simp
  rw [jacobiTheta₂_functional_equation, jacobiTheta₂'_functional_equation, hz] at h
  have hf : (fun j : ℤ => (((x : ℤ) + m * j : ℤ) : ℂ) * ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ)) =
      fun i : ℤ => ee ((x : ℂ) ^ 2 * τ) * ((x : ℂ) * jacobiTheta₂_term i (2 * m * x * τ) (2 * m ^ 2 * τ) +
        (m : ℂ) / (2 * π * I) * jacobiTheta₂'_term i (2 * m * x * τ) (2 * m ^ 2 * τ)) := by
    funext j
    rw [ee_class x j m τ]
    simp only [jacobiTheta₂'_term]
    have : (m : ℂ) / (2 * π * I) * (2 * π * I * (j : ℂ)) = m * j := by field_simp
    push_cast
    linear_combination (-(ee ((x : ℂ) ^ 2 * τ) * jacobiTheta₂_term j (2 * m * x * τ) (2 * m ^ 2 * τ))) * this
  rw [hf]
  convert_to HasSum _ (ee ((x : ℂ) ^ 2 * τ) *
      ((x : ℂ) *
          (1 / (-I * (2 * (m : ℂ) ^ 2 * τ)) ^ (1 / 2 : ℂ) * cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ)) *
            jacobiTheta₂ (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ))) +
        (m : ℂ) / (2 * π * I) *
          (1 / (-I * (2 * (m : ℂ) ^ 2 * τ)) ^ (1 / 2 : ℂ) * cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ)) /
              (2 * (m : ℂ) ^ 2 * τ) *
            (jacobiTheta₂' (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) -
              2 * π * I * (2 * m * x * τ) * jacobiTheta₂ (x / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)))))) using 1
  · have e : ∀ Y : ℂ, (-2 * I * τ) ^ (-(1 / 2 : ℂ)) * (2 * τ * m)⁻¹ * (m : ℂ)⁻¹ * Y =
        ((-2 * I * τ) ^ (-(1 / 2 : ℂ)) * (m : ℂ)⁻¹) * ((2 * τ * m)⁻¹ * Y) := fun Y => by ring
    rw [e, ← prefactor hm hτ x]
    generalize jacobiTheta₂ ((x : ℂ) / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) = A
    generalize jacobiTheta₂' ((x : ℂ) / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) = B
    generalize cexp (-π * I * (2 * m * x * τ) ^ 2 / (2 * (m : ℂ) ^ 2 * τ)) = E
    generalize (1 / (-I * (2 * (m : ℂ) ^ 2 * τ)) ^ (1 / 2 : ℂ)) = P
    generalize ee ((x : ℂ) ^ 2 * τ) = G
    field_simp
    ring
  · exact h

theorem term_dual {m : ℕ} (hm : 0 < m) {τ : ℂ} (hτ : τ ≠ 0) (x : ℕ) (n : ℤ) :
    jacobiTheta₂_term n ((x : ℂ) / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) =
      ee ((n : ℂ) * x / m) * ee (-((n : ℂ) ^ 2 / (4 * (m : ℂ) ^ 2 * τ))) := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold ee jacobiTheta₂_term
  rw [← Complex.exp_add]
  congr 1
  field_simp
  ring

theorem class_nu {m ν : ℕ} (hm : 0 < m) (hν : ν ≤ 1) {τ : ℂ} (hτ : 0 < τ.im) (x : ℕ) :
    ∃ R : ℂ,
      HasSum (fun j : ℤ => (((x : ℤ) + m * j : ℤ) : ℂ) ^ ν * ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ))
        ((-2 * I * τ) ^ (-(1 / 2 : ℂ)) * ((2 * τ * m) ^ ν)⁻¹ * (m : ℂ)⁻¹ * R) ∧
      HasSum (fun n : ℤ => (n : ℂ) ^ ν * (ee ((n : ℂ) * x / m) * ee (-((n : ℂ) ^ 2 / (4 * (m : ℂ) ^ 2 * τ))))) R := by
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpi : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
  have hT : 0 < (-1 / (2 * (m : ℂ) ^ 2 * τ)).im := by
    have h := im_pos_scaled_upper_half_plane hm hτ
    have h' : -1 / (2 * (m : ℂ) ^ 2 * τ) = -(2 * (m : ℂ) ^ 2 * τ)⁻¹ := by ring
    rw [h', Complex.neg_im, Complex.inv_im]
    have hne : 2 * (m : ℂ) ^ 2 * τ ≠ 0 := by
      intro h0; rw [h0] at h; simp at h
    have := Complex.normSq_pos.mpr hne
    simp only [neg_div, neg_neg]
    positivity
  interval_cases ν
  · refine ⟨jacobiTheta₂ ((x : ℂ) / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)), ?_, ?_⟩
    · simpa using class_zero hm hτ x
    · have h := hasSum_jacobiTheta₂_term ((x : ℂ) / m) hT
      simpa only [pow_zero, one_mul, term_dual hm hτ0] using h
  · refine ⟨jacobiTheta₂' ((x : ℂ) / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) / (2 * π * I), ?_, ?_⟩
    · simpa using class_one hm hτ x
    · have h := (hasSum_jacobiTheta₂'_term ((x : ℂ) / m) hT).div_const (2 * π * I)
      have hf : (fun n : ℤ => (n : ℂ) ^ 1 * (ee ((n : ℂ) * x / m) * ee (-((n : ℂ) ^ 2 / (4 * (m : ℂ) ^ 2 * τ))))) =
          fun n : ℤ => jacobiTheta₂'_term n ((x : ℂ) / m) (-1 / (2 * (m : ℂ) ^ 2 * τ)) / (2 * π * I) := by
        funext n
        rw [jacobiTheta₂'_term, term_dual hm hτ0]
        field_simp
      rw [hf]
      exact h

end GlobalTheory.CompanionTheory.HalfTheta

open GlobalTheory.CompanionTheory.HalfTheta in

theorem GlobalTheory.CompanionTheory.HalfTheta.t1 : T1 := by
  intro Q m ν τ hm hν hτ hQ
  choose R hR₁ hR₂ using fun x : ℕ => class_nu hm hν hτ x
  set C : ℂ := (-2 * Complex.I * τ) ^ (-(1 / 2 : ℂ)) * ((2 * τ * m) ^ ν)⁻¹ * (m : ℂ)⁻¹ with hC
  have hmZ : (0 : ℤ) < m := by exact_mod_cast hm
  have hper : ∀ (x : ℤ) (j : ℤ), Q (x + m * j) = Q x := by
    intro x j
    have hp : Function.Periodic Q (m : ℤ) := fun y => hQ y
    have := (hp.int_mul j) x
    simpa [mul_comm] using this
  let G : ℤ → ℂ := fun n => Q n * (n : ℂ) ^ ν * ee ((n : ℂ) ^ 2 * τ)
  have hslice : ∀ x ∈ Finset.range m,
      HasSum (fun n : ℤ => if n % m = (x : ℤ) then G n else 0) (Q x * (C * R x)) := by
    intro x hx
    have hxm : (x : ℤ) < m := by exact_mod_cast Finset.mem_range.mp hx
    have hinj : Function.Injective (fun j : ℤ => (x : ℤ) + m * j) := by
      intro a b hab
      have : (m : ℤ) * a = m * b := by simpa using hab
      exact mul_left_cancel₀ hmZ.ne' this
    refine (hinj.hasSum_iff ?_).mp ?_
    · intro n hn
      rw [if_neg]
      intro hnx
      exact hn ⟨n / m, by rw [← hnx]; exact Int.emod_add_mul_ediv n m⟩
    · have hmod : ∀ j : ℤ, ((x : ℤ) + m * j) % m = x := by
        intro j
        rw [Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by positivity) hxm
      have hf : ((fun n : ℤ => if n % m = (x : ℤ) then G n else 0) ∘ fun j : ℤ => (x : ℤ) + m * j) =
          fun j : ℤ => Q x * ((((x : ℤ) + m * j : ℤ) : ℂ) ^ ν * ee ((((x : ℤ) + m * j : ℤ) : ℂ) ^ 2 * τ)) := by
        funext j
        simp only [Function.comp, hmod j, if_true, G, hper]
        ring
      rw [hf]
      exact (hR₁ x).mul_left _
  have hsum := hasSum_sum hslice
  have hG : (fun n : ℤ => ∑ x ∈ Finset.range m, if n % m = (x : ℤ) then G n else 0) = G := by
    funext n
    have h0 : 0 ≤ n % m := Int.emod_nonneg _ hmZ.ne'
    have h1 : n % m < m := Int.emod_lt_of_pos _ hmZ
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h0
    have hkm : k < m := by omega
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro b _ hb
      rw [if_neg]
      omega
    · intro hk'
      exact absurd (Finset.mem_range.mpr hkm) hk'
  rw [hG] at hsum
  have hth : th Q ν τ = ∑ x ∈ Finset.range m, Q x * (C * R x) := hsum.tsum_eq
  have hdual : HasSum (fun n : ℤ => (∑ x ∈ Finset.range m, Q x * ee (n * x / m)) * (n : ℂ) ^ ν *
      ee (-((n : ℂ) ^ 2 / (4 * (m : ℂ) ^ 2 * τ)))) (∑ x ∈ Finset.range m, Q x * R x) := by
    have h := hasSum_sum fun x (_ : x ∈ Finset.range m) => (hR₂ x).mul_left (Q x)
    have hf : (fun n : ℤ => (∑ x ∈ Finset.range m, Q x * ee (n * x / m)) * (n : ℂ) ^ ν *
        ee (-((n : ℂ) ^ 2 / (4 * (m : ℂ) ^ 2 * τ)))) =
        fun n : ℤ => ∑ x ∈ Finset.range m, Q x * ((n : ℂ) ^ ν * (ee ((n : ℂ) * x / m) *
          ee (-((n : ℂ) ^ 2 / (4 * (m : ℂ) ^ 2 * τ))))) := by
      funext n
      rw [Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [hf]
    exact h
  rw [hth, hdual.tsum_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring
