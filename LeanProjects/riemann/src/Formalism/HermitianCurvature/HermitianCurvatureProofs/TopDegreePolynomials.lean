import Formalism.HermitianCurvature.LevelRecursionCondNeeded

namespace Formalism.FourierDecayAlt.P.TopDegreePolynomials

open Finset Polynomial Formalism.FourierDecayAlt.F7

section

variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

theorem evR_smul (P : R[X]) (a : ℕ) (ha : P.natDegree ≤ a) (Y : ℝ) (X : M) :
    evR P Y • X = ∑ i ∈ range (a + 1), ((Y : ℂ) ^ i) • (P.coeff i • X) := by
  unfold evR
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le ha), Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← map_pow, ← Algebra.commutes, mul_smul, algebraMap_smul]

end

theorem isTop_sub {W W' : ℝ → ℂ} {d : ℕ} {c c' : ℂ} (h : IsTopCoeff W d c)
    (h' : IsTopCoeff W' d c') : IsTopCoeff (fun Y => W Y - W' Y) d (c - c') := by
  obtain ⟨P, hd, hc, hP⟩ := h
  obtain ⟨P', hd', hc', hP'⟩ := h'
  exact ⟨P - P', (natDegree_sub_le_of_le hd hd').trans (by simp), by rw [coeff_sub, hc, hc'],
    fun Y => by simp only [eval_sub, hP, hP']⟩

theorem isTop_const_mul {W : ℝ → ℂ} {d : ℕ} {c : ℂ} (k : ℂ) (h : IsTopCoeff W d c) :
    IsTopCoeff (fun Y => k * W Y) d (k * c) := by
  obtain ⟨P, hd, hc, hP⟩ := h
  exact ⟨C k * P, (natDegree_C_mul_le _ _).trans hd, by rw [coeff_C_mul, hc],
    fun Y => by simp only [eval_mul, eval_C, hP]⟩

theorem natDegree_mono (h : ℂ) (i j : ℕ) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).natDegree = i + j := by
  rw [Monic.natDegree_mul (monic_X_pow i) ((monic_X_add_C h).pow j), natDegree_X_pow,
    Monic.natDegree_pow (monic_X_add_C h), natDegree_X_add_C, mul_one]

theorem coeff_mono (h : ℂ) (a b i j : ℕ) (hi : i ≤ a) (hj : j ≤ b) :
    ((X : ℂ[X]) ^ i * (X + C h) ^ j).coeff (a + b) = if i = a ∧ j = b then 1 else 0 := by
  have hm : ((X : ℂ[X]) ^ i * (X + C h) ^ j).Monic := (monic_X_pow i).mul ((monic_X_add_C h).pow j)
  split_ifs with hij
  · obtain ⟨rfl, rfl⟩ := hij
    have := hm.coeff_natDegree
    rwa [natDegree_mono] at this
  · apply coeff_eq_zero_of_natDegree_lt
    rw [natDegree_mono]
    omega

end Formalism.FourierDecayAlt.P.TopDegreePolynomials

namespace Formalism.FourierDecayAlt.P

open Finset Polynomial Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.TopDegreePolynomials

theorem pairing_top_degree : Formalism.FourierDecayAlt.F7.PairTop := by
  intro R M _ _ _ _ _ _ Ξ P₁ P₂ a b h X X' ha hb
  refine ⟨∑ i ∈ range (a + 1), ∑ j ∈ range (b + 1),
    C (Ξ (P₁.coeff i • X) (P₂.coeff j • X')) * ((Polynomial.X : ℂ[X]) ^ i *
      (Polynomial.X + C (h : ℂ)) ^ j), ?_, ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_mono]
    have := Finset.mem_range.mp hi
    have := Finset.mem_range.mp hj
    omega
  · rw [finsetSum_coeff]
    rw [Finset.sum_eq_single a]
    · rw [finsetSum_coeff, Finset.sum_eq_single b]
      · rw [coeff_C_mul, coeff_mono _ _ _ _ _ le_rfl le_rfl]; simp
      · intro j hj hjb
        rw [coeff_C_mul, coeff_mono _ _ _ _ _ le_rfl (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
        simp [hjb]
      · intro hb'; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self b)) hb'
    · intro i hi hia
      rw [finsetSum_coeff]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [coeff_C_mul, coeff_mono _ _ _ _ _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
      simp [hia]
    · intro ha'; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self a)) ha'
  · intro Y
    simp only []
    rw [evR_smul P₁ a ha, evR_smul P₂ b hb, map_sum Ξ, LinearMap.sum_apply, eval_finsetSum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul Ξ, LinearMap.smul_apply, map_smulₛₗ]
    simp only [eval_mul, eval_C, eval_pow, eval_X, eval_add, smul_eq_mul, map_pow,
      map_add, Complex.conj_ofReal, Complex.ofReal_add]
    ring

theorem j_pairing_formula : Formalism.FourierDecayAlt.F7.JPairing := by
  intro R M _ _ _ _ _ _ Ξ A B Av Bv s Y Y' X X'
  simp [pair2, act2, vec, Formalism.YangianSpanCharacter.T.J, Formalism.YangianSpanCharacter.T.Uinv, Fin.sum_univ_two, Matrix.mul_apply, add_smul,
    mul_smul, algebraMap_smul]
  ring

theorem plane_wave_top_degree : Formalism.FourierDecayAlt.F7.PlaneWaveTop := by
  intro R M _ _ _ _ _ _ Ξ n A B Av Bv s X X' hS hSv
  obtain ⟨hA, hAn, hB⟩ := hS
  obtain ⟨hAv, hAvn, hBv⟩ := hSv
  have cA : A.coeff n = 1 := by rw [← hAn]; exact hA.coeff_natDegree
  have cAv : Av.coeff n = 1 := by rw [← hAvn]; exact hAv.coeff_natDegree
  have cB : B.coeff n = 0 := coeff_eq_zero_of_degree_lt hB
  have cBv : Bv.coeff n = 0 := coeff_eq_zero_of_degree_lt hBv
  have dB : B.natDegree ≤ n := natDegree_le_of_degree_le hB.le
  have dBv : Bv.natDegree ≤ n := natDegree_le_of_degree_le hBv.le
  have h1 := pairing_top_degree R M Ξ (B + C (algebraMap ℂ R s) * A) Av n n 1 X X'
    (natDegree_add_le_of_degree_le dB ((natDegree_C_mul_le _ _).trans hAn.le)) hAvn.le
  have h2 := pairing_top_degree R M Ξ A Bv n n 1 X X' hAn.le dBv
  have h3 := isTop_sub h1 h2
  rw [two_mul]
  convert h3 using 1
  · funext Y
    rw [j_pairing_formula R M Ξ A B Av Bv s Y (Y + 1) X X']
    simp [evR, eval_add, eval_C_mul]
  · simp [cA, cAv, cB, cBv, algebraMap_smul]

theorem lift_top_degree : Formalism.FourierDecayAlt.F7.LiftTop := by
  intro R M _ _ _ _ _ _ Ξ n s A B Av Bv A₀ A₀v e t t' h X X' _ he ht ht' hA hAn hAv hAvn
    hA₀ hA₀n hA₀v hA₀vn hB hBv
  have cA : A.coeff (n + s) = 1 := by rw [← hAn]; exact hA.coeff_natDegree
  have cAv : Av.coeff (n + s) = 1 := by rw [← hAvn]; exact hAv.coeff_natDegree
  have cA₀ : A₀.coeff n = 1 := by rw [← hA₀n]; exact hA₀.coeff_natDegree
  have cA₀v : A₀v.coeff n = 1 := by rw [← hA₀vn]; exact hA₀v.coeff_natDegree
  have h1 := isTop_const_mul (e * t⁻¹)
    (pairing_top_degree R M Ξ A₀ Av n (n + s) h X X' hA₀n.le hAvn.le)
  have h2 := isTop_const_mul (e * t'⁻¹)
    (pairing_top_degree R M Ξ A A₀v (n + s) n h X X' hAn.le hA₀vn.le)
  have e1 : n + (n + s) = 2 * n + s := by ring
  have e2 : n + s + n = 2 * n + s := by ring
  rw [e1] at h1
  rw [e2] at h2
  have h3 := isTop_sub h1 h2
  have hce : (starRingEnd ℂ) e = e := by
    rcases he with rfl | rfl <;> simp
  convert h3 using 1
  · funext Y
    have := j_pairing_formula R M Ξ A B Av Bv 0 Y (Y + h) X X'
    have hU : Formalism.YangianSpanCharacter.T.Uinv (A := R) (0 : ℂ) = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Formalism.YangianSpanCharacter.T.Uinv]
    rw [hU, mul_one] at this
    rw [this, map_zero, zero_mul, add_zero, hB, hBv, map_smul Ξ, LinearMap.smul_apply,
      LinearMap.map_smulₛₗ (Ξ (evR A Y • X))]
    simp [hce]
  · simp [cA, cAv, cA₀, cA₀v]
    ring

end Formalism.FourierDecayAlt.P
