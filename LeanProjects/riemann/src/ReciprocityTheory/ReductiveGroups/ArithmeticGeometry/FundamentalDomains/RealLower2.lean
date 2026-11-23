import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HermCOrthonormalCoordinates

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

lemma real_upper {ρ α β Q : ℝ} (hρ1 : ρ < 1) (hρ0 : 0 ≤ ρ)
    (hQ : Q * (1 - ρ ^ 2) ≤ (α + ρ * β) ^ 2) :
    2 * Q - (α ^ 2 - β ^ 2) ≤ (1 + ρ) / (1 - ρ) * (α ^ 2 + β ^ 2) := by
  have h1 : 0 < 1 - ρ := by linarith
  have h2 : 0 < 1 + ρ := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  nlinarith [mul_nonneg hρ0 (sq_nonneg (α - β)), mul_le_mul_of_nonneg_left hQ h2.le]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma mj_xZ_zero (x : Frame X.Ψ r) : X.xZ x 0 = x := by
  funext τ
  have h1 : X.lowBlock 0 τ = 1 := by
    ext a b
    simp [Data.lowBlock, Matrix.one_apply]
  show (mat x τ * X.lowBlock 0 τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [h1, Matrix.mul_one]
  rfl

private lemma nsq_add_fundamental_domains {n : ℕ} (p q : Fin n → ℂ) :
    nsq (p + q) = nsq p + 2 * (mjip p q).re + nsq q := by
  rw [show p + q = p - ((-1 : ℝ) : ℂ) • q by simp, mjnsq_sub_smul]
  ring

private lemma re_mjip_comm {n : ℕ} (p q : Fin n → ℂ) : (mjip q p).re = (mjip p q).re := by
  simp only [mjip, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.mul_re]
  ring

private lemma mjip_sub_left {n : ℕ} (p q δ : Fin n → ℂ) :
    mjip (p - q) δ = mjip p δ - mjip q δ := by
  simp [mjip, sub_mul, Finset.sum_sub_distrib]

private lemma re_mjip_le_sqrt_nsq_mul {n : ℕ} (p q : Fin n → ℂ) :
    (mjip p q).re ≤ Real.sqrt (nsq p) * Real.sqrt (nsq q) :=
  (Complex.re_le_norm _).trans (mjip_norm_le p q)

private lemma neg_re_mjip_le_sqrt_nsq_mul {n : ℕ} (p q : Fin n → ℂ) :
    -(mjip p q).re ≤ Real.sqrt (nsq p) * Real.sqrt (nsq q) :=
  (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans (mjip_norm_le p q))

private lemma sqrt_nsq_mulVec_le_opN_mul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (v : Fin n → ℂ) :
    Real.sqrt (nsq (A *ᵥ v)) ≤ Data.opN A * Real.sqrt (nsq v) := by
  rw [← Real.sqrt_sq (opN_nonneg A), ← Real.sqrt_mul (sq_nonneg _)]
  exact Real.sqrt_le_sqrt (nsq_mulVec_le_opN A v)

set_option maxHeartbeats 800000 in

theorem mj_bounds {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ : ρ ≤ 1 / 10) {Z : X.Coord} (hZ : X.zN Z ≤ ρ) (hy : X.xZ x Z ∈ X.dom) (τ : X.Ψ)
    (v : Fin r → ℂ) :
    (1 - ρ) / (1 + ρ) * X.maj x τ v ≤ X.maj (X.xZ x Z) τ v ∧
      X.maj (X.xZ x Z) τ v ≤ (1 + ρ) / (1 - ρ) * X.maj x τ v := by
  obtain ⟨w, rfl⟩ : ∃ w, v = mat x τ *ᵥ w := ⟨(mat x τ)⁻¹ *ᵥ v, by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr ((X.mem_dom_iff x).1 hx τ).1), Matrix.one_mulVec]⟩
  have hx0 : X.xZ x 0 ∈ X.dom := by rw [mj_xZ_zero]; exact hx
  obtain ⟨γ0, h0maj, h0id⟩ := mj_coord X ho 0 hx0 τ w
  rw [mj_xZ_zero] at h0maj
  have hZ0 : Matrix.of ((0 : X.Coord) τ) = 0 := by ext; rfl
  have hγ0 : γ0 = mjpa X w := by
    funext d
    have := h0id (Pi.single d 1)
    simp only [hZ0, Matrix.zero_mulVec, mjip_zero_right, sub_zero, mjip_single] at this
    exact this.symm
  have hmx : X.maj x τ (mat x τ *ᵥ w) = nsq (mjpa X w) + nsq (mjpb X w) := by
    rw [h0maj, hZ0, Matrix.zero_mulVec, nsq_zero', hγ0]
    ring
  obtain ⟨γ, hmaj, hid⟩ := mj_coord X ho Z hy τ w
  rw [hmx, hmaj]
  have hk0 : 0 ≤ Data.opN (Matrix.of (Z τ)) := opN_nonneg _
  have hkρ : Data.opN (Matrix.of (Z τ)) ≤ ρ := (opN_le_zN X Z τ).trans hZ
  have hs2 : nsq (Matrix.of (Z τ) *ᵥ γ) ≤ Data.opN (Matrix.of (Z τ)) ^ 2 * nsq γ :=
    nsq_mulVec_le_opN _ _
  have hS : Real.sqrt (nsq (Matrix.of (Z τ) *ᵥ γ)) ≤ Data.opN (Matrix.of (Z τ)) * Real.sqrt (nsq γ) :=
    sqrt_nsq_mulVec_le_opN_mul _ _
  have hdid : ∀ δ, mjip (mjpa X w - γ) δ =
      mjip (mjpb X w - Matrix.of (Z τ) *ᵥ γ) (Matrix.of (Z τ) *ᵥ δ) := by
    intro δ
    rw [mjip_sub_left, mjip_sub_left]
    linear_combination hid δ
  set Zm := Matrix.of (Z τ) with hZm
  set k := Data.opN Zm with hkdef
  set d := mjpa X w - γ with hd
  set t := mjpb X w - Zm *ᵥ γ with ht
  have hG0 := Real.sqrt_nonneg (nsq γ)
  have hT0 := Real.sqrt_nonneg (nsq t)
  have hD0 := Real.sqrt_nonneg (nsq d)
  have hG2 := Real.sq_sqrt (nsq_nonneg γ)
  have hT2 := Real.sq_sqrt (nsq_nonneg t)
  have hD2 := Real.sq_sqrt (nsq_nonneg d)
  have hDs : Real.sqrt (nsq d) ≤ k * Real.sqrt (nsq t) := by
    have h1 : nsq d = (mjip t (Zm *ᵥ d)).re := by rw [← hdid, mjip_self, Complex.ofReal_re]
    have h2 := re_mjip_le_sqrt_nsq_mul t (Zm *ᵥ d)
    have h4 : Real.sqrt (nsq (Zm *ᵥ d)) ≤ k * Real.sqrt (nsq d) := sqrt_nsq_mulVec_le_opN_mul Zm d
    have h5 : Real.sqrt (nsq d) ^ 2 ≤ Real.sqrt (nsq t) * (k * Real.sqrt (nsq d)) := by
      calc Real.sqrt (nsq d) ^ 2 = nsq d := hD2
        _ = (mjip t (Zm *ᵥ d)).re := h1
        _ ≤ _ := h2.trans (mul_le_mul_of_nonneg_left h4 hT0)
    rcases eq_or_lt_of_le hD0 with h | h
    · rw [← h]
      positivity
    · nlinarith
  have hdd : nsq d ≤ k ^ 2 * nsq t := by
    calc nsq d = Real.sqrt (nsq d) ^ 2 := hD2.symm
      _ ≤ (k * Real.sqrt (nsq t)) ^ 2 := pow_le_pow_left₀ hD0 hDs 2
      _ = k ^ 2 * nsq t := by rw [mul_pow, hT2]
  have hAe : nsq (mjpa X w) = nsq γ + 2 * (mjip γ d).re + nsq d := by
    rw [show mjpa X w = γ + d by rw [hd]; abel, nsq_add_fundamental_domains]
  have hBe : nsq (mjpb X w) = nsq (Zm *ᵥ γ) + 2 * (mjip (Zm *ᵥ γ) t).re + nsq t := by
    rw [show mjpb X w = Zm *ᵥ γ + t by rw [ht]; abel, nsq_add_fundamental_domains]
  have hcross : (mjip γ d).re = (mjip (Zm *ᵥ γ) t).re := by
    rw [re_mjip_comm d γ, hdid γ, re_mjip_comm (Zm *ᵥ γ) t]
  have hs2' : nsq (Zm *ᵥ γ) ≤ k ^ 2 * nsq γ := hs2
  have hS' : Real.sqrt (nsq (Zm *ᵥ γ)) ≤ k * Real.sqrt (nsq γ) := hS
  have hk1 : k < 1 := by linarith
  refine ⟨?_, ?_⟩
  · have hlow : (1 - k ^ 2) * (nsq γ + nsq t) ≤
        2 * (nsq γ - nsq (Zm *ᵥ γ)) - (nsq (mjpa X w) - nsq (mjpb X w)) := by
      rw [hAe, hBe, hcross]
      nlinarith [hs2', hdd]
    have r1 : (mjip γ d).re ≤ Real.sqrt (nsq γ) * (k * Real.sqrt (nsq t)) :=
      (re_mjip_le_sqrt_nsq_mul γ d).trans (mul_le_mul_of_nonneg_left hDs hG0)
    have r2 : (mjip (Zm *ᵥ γ) t).re ≤ (k * Real.sqrt (nsq γ)) * Real.sqrt (nsq t) :=
      (re_mjip_le_sqrt_nsq_mul (Zm *ᵥ γ) t).trans (mul_le_mul_of_nonneg_right hS' hT0)
    have hAB : nsq (mjpa X w) + nsq (mjpb X w) ≤ (1 + k) ^ 2 * (nsq γ + nsq t) := by
      rw [hAe, hBe]
      nlinarith [mul_nonneg hk0 (sq_nonneg (Real.sqrt (nsq γ) - Real.sqrt (nsq t)))]
    have hc : (1 - ρ) / (1 + ρ) ≤ (1 - k) / (1 + k) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have hAB0 : 0 ≤ nsq (mjpa X w) + nsq (mjpb X w) := add_nonneg (nsq_nonneg _) (nsq_nonneg _)
    calc (1 - ρ) / (1 + ρ) * (nsq (mjpa X w) + nsq (mjpb X w))
        ≤ (1 - k) / (1 + k) * (nsq (mjpa X w) + nsq (mjpb X w)) := mul_le_mul_of_nonneg_right hc hAB0
      _ ≤ (1 - k) / (1 + k) * ((1 + k) ^ 2 * (nsq γ + nsq t)) :=
          mul_le_mul_of_nonneg_left hAB (div_nonneg (by linarith) (by linarith))
      _ = (1 - k ^ 2) * (nsq γ + nsq t) := by
          field_simp
          ring
      _ ≤ _ := hlow
  · have hQid : nsq γ - nsq (Zm *ᵥ γ) = (mjip (mjpa X w) γ).re - (mjip (mjpb X w) (Zm *ᵥ γ)).re := by
      have := congrArg Complex.re (hid γ)
      simp only [Complex.sub_re, mjip_self, Complex.ofReal_re] at this
      linarith
    have r3 := re_mjip_le_sqrt_nsq_mul (mjpa X w) γ
    have r4 := neg_re_mjip_le_sqrt_nsq_mul (mjpb X w) (Zm *ᵥ γ)
    have hβ0 := Real.sqrt_nonneg (nsq (mjpb X w))
    have hα0 := Real.sqrt_nonneg (nsq (mjpa X w))
    have r5 : Real.sqrt (nsq (mjpb X w)) * Real.sqrt (nsq (Zm *ᵥ γ)) ≤
        Real.sqrt (nsq (mjpb X w)) * (ρ * Real.sqrt (nsq γ)) :=
      mul_le_mul_of_nonneg_left (hS'.trans (mul_le_mul_of_nonneg_right hkρ hG0)) hβ0
    have hQle : nsq γ - nsq (Zm *ᵥ γ) ≤
        (Real.sqrt (nsq (mjpa X w)) + ρ * Real.sqrt (nsq (mjpb X w))) * Real.sqrt (nsq γ) := by
      rw [hQid]
      linarith [r3, r4, r5]
    have hkk : k ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hk0 hkρ 2
    have hQge : (1 - ρ ^ 2) * nsq γ ≤ nsq γ - nsq (Zm *ᵥ γ) := by
      linarith [hs2', mul_le_mul_of_nonneg_right hkk (nsq_nonneg γ)]
    have hρ2 : 0 ≤ 1 - ρ ^ 2 := by
      have : ρ ^ 2 ≤ ρ := by
        rw [sq]
        exact mul_le_of_le_one_left hρ0.le (by linarith)
      linarith
    have hQ0 : 0 ≤ nsq γ - nsq (Zm *ᵥ γ) := le_trans (mul_nonneg hρ2 (nsq_nonneg γ)) hQge
    have hup : (nsq γ - nsq (Zm *ᵥ γ)) * (1 - ρ ^ 2) ≤
        (Real.sqrt (nsq (mjpa X w)) + ρ * Real.sqrt (nsq (mjpb X w))) ^ 2 := by
      set s := Real.sqrt (nsq (mjpa X w)) + ρ * Real.sqrt (nsq (mjpb X w)) with hs
      set Q := nsq γ - nsq (Zm *ᵥ γ) with hQ
      rcases eq_or_lt_of_le hQ0 with hq | hq
      · rw [← hq, zero_mul]
        positivity
      · have hsq : Q ^ 2 ≤ (s * Real.sqrt (nsq γ)) ^ 2 := pow_le_pow_left₀ hQ0 hQle 2
        rw [mul_pow, hG2] at hsq
        nlinarith [mul_le_mul_of_nonneg_left hQge (sq_nonneg s), mul_le_mul_of_nonneg_right hsq hρ2]
    have := real_upper (ρ := ρ) (α := Real.sqrt (nsq (mjpa X w))) (β := Real.sqrt (nsq (mjpb X w)))
      (Q := nsq γ - nsq (Zm *ᵥ γ)) (by linarith) hρ0.le hup
    rwa [Real.sq_sqrt (nsq_nonneg _), Real.sq_sqrt (nsq_nonneg _)] at this

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
