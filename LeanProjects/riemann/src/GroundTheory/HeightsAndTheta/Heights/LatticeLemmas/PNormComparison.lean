import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights
open scoped ComplexOrder MatrixOrder

noncomputable section

theorem re_det_le_of_posSemidef_smul_sub {n : Type*} [Fintype n] [DecidableEq n]
    {G G' : Matrix n n ℂ} (hG : G.PosDef) (hG' : G'.PosSemidef) (c : ℝ)
    (hc : (c • G - G').PosSemidef) : (det G').re ≤ c ^ Fintype.card n * (det G).re := by
  obtain ⟨P, hP⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.posSemidef.nonneg
  rw [star_eq_conjTranspose] at hP
  have hdetG : det G = star (det P) * det P := by
    rw [hP, det_mul, det_conjTranspose]
  have hPne : det P ≠ 0 := by
    intro h0
    have := hG.det_pos.ne'
    rw [hdetG, h0, mul_zero] at this
    exact this rfl
  have hU : IsUnit (det P) := isUnit_iff_ne_zero.mpr hPne
  set Q := P⁻¹ with hQ
  have hQP : Q * P = 1 := nonsing_inv_mul P hU
  have hPQ : P * Q = 1 := mul_nonsing_inv P hU
  set B := Qᴴ * G' * Q with hB
  have hBpsd : B.PosSemidef := hG'.conjTranspose_mul_mul_same Q
  have hG'eq : G' = Pᴴ * B * P := by
    calc G' = (Q * P)ᴴ * G' * (Q * P) := by rw [hQP, conjTranspose_one, one_mul, mul_one]
      _ = Pᴴ * B * P := by rw [conjTranspose_mul, hB]; simp only [Matrix.mul_assoc]
  have hQGQ : Qᴴ * G * Q = 1 := by
    calc Qᴴ * G * Q = (P * Q)ᴴ * (P * Q) := by
          rw [hP, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPQ, conjTranspose_one, one_mul]
  have hCB : (c • (1 : Matrix n n ℂ) - B).PosSemidef := by
    have := hc.conjTranspose_mul_mul_same Q
    rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hQGQ] at this
  have heig : ∀ i, hBpsd.1.eigenvalues i ≤ c := by
    intro i
    set u : n → ℂ := ⇑(hBpsd.1.eigenvectorBasis i)
    have h1 := hCB.re_dotProduct_nonneg u
    have hu : star u ⬝ᵥ u = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hBpsd.1.eigenvectorBasis.orthonormal.1 i]
      simp
    rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, hu, map_sub,
      ← hBpsd.1.eigenvalues_eq i] at h1
    simpa using h1
  have hdetB : (det B).re ≤ c ^ Fintype.card n := by
    rw [hBpsd.1.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    change (((∏ i, hBpsd.1.eigenvalues i : ℝ) : ℂ)).re ≤ _
    rw [Complex.ofReal_re]
    calc ∏ i, hBpsd.1.eigenvalues i ≤ ∏ _i : n, c :=
          Finset.prod_le_prod (fun i _ ↦ hBpsd.eigenvalues_nonneg i) (fun i _ ↦ heig i)
      _ = c ^ Fintype.card n := by rw [Finset.prod_const, Finset.card_univ]
  have hstar : star (det P) * det P = ((Complex.normSq (det P) : ℝ) : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj (det P)
  have hdetG' : det G' = det B * ((Complex.normSq (det P) : ℝ) : ℂ) := by
    rw [hG'eq, det_mul, det_mul, det_conjTranspose, ← hstar]; ring
  rw [hdetG', hdetG, hstar, Complex.re_mul_ofReal, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right hdetB (Complex.normSq_nonneg _)

variable {K : Type*} [Field K] [NumberField K]

theorem gramDet_le_of_norm_le {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h h' : HermitianMetric K E) (σ : K →+* ℂ) (A : ℝ)
    (hA : ∀ x : Fibre σ E, ‖FibreSpace.equiv h' σ x‖ ≤ A * ‖FibreSpace.equiv h σ x‖)
    {r : ℕ} {s : Fin r → E} (hs : LinearIndependent (𝓞 K) s) :
    gramDet h' σ s ≤ (max A 0 ^ 2) ^ r * gramDet h σ s := by
  let L : FibreSpace h σ →ₗ[ℂ] FibreSpace h' σ :=
    (FibreSpace.equiv h' σ).toLinearMap ∘ₗ (FibreSpace.equiv h σ).symm.toLinearMap
  have hL : ∀ y, ‖L y‖ ≤ A * ‖y‖ := by
    intro y
    have := hA ((FibreSpace.equiv h σ).symm y)
    rwa [LinearEquiv.apply_symm_apply] at this
  let f := L.mkContinuous A hL
  have hf : ‖f‖ ≤ max A 0 := LinearMap.mkContinuous_norm_le' L hL
  set v : Fin r → FibreSpace h σ := fun i ↦ fibreVec h σ (s i)
  have hfv : (⇑f ∘ v) = fun i ↦ fibreVec h' σ (s i) := rfl
  have hpsd := posSemidef_opNorm_smul_gram_sub_gram v f
  rw [hfv] at hpsd
  have hmain := re_det_le_of_posSemidef_smul_sub
    (posDef_gram_of_linearIndependent (linearIndependent_fibreVec h σ hs))
    (posSemidef_gram ℂ _) _ hpsd
  rw [Fintype.card_fin] at hmain
  have hg : 0 < gramDet h σ s := gramDet_pos h σ hs
  calc gramDet h' σ s ≤ (‖f‖ ^ 2) ^ r * gramDet h σ s := hmain
    _ ≤ (max A 0 ^ 2) ^ r * gramDet h σ s := by
      gcongr

theorem NormComparison.proof : NormComparison.Statement := by
  intro K _ _ M h' A hA
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := M.carrier)
  have hlog : ∀ σ : K →+* ℂ, Real.log (gramDet h' σ s) ≤
      2 * (Module.finrank (𝓞 K) M.carrier : ℝ) * Real.log (A σ) + Real.log (gramDet M.metric σ s) := by
    intro σ
    have hle := gramDet_le_of_norm_le M.metric h' σ (A σ) (hA σ) hs
    have hg : 0 < gramDet M.metric σ s := gramDet_pos _ σ hs
    have hg' : 0 < gramDet h' σ s := gramDet_pos _ σ hs
    rcases Nat.eq_zero_or_pos (Module.finrank (𝓞 K) M.carrier) with hr | hr
    · have h1 : (max (A σ) 0 ^ 2) ^ Module.finrank (𝓞 K) M.carrier = 1 := by rw [hr, pow_zero]
      have h0 : ((Module.finrank (𝓞 K) M.carrier : ℕ) : ℝ) = 0 := by exact_mod_cast hr
      rw [h1, one_mul] at hle
      rw [h0, mul_zero, zero_mul, zero_add]
      exact Real.log_le_log hg' hle
    · have hpos : 0 < (max (A σ) 0 ^ 2) ^ Module.finrank (𝓞 K) M.carrier :=
        (pos_iff_pos_of_mul_pos (lt_of_lt_of_le hg' hle)).mpr hg
      have hmax : 0 < max (A σ) 0 := by
        rcases (le_max_right (A σ) 0).lt_or_eq with h1 | h1
        · exact h1
        · rw [← h1] at hpos; simp [zero_pow (Nat.pos_iff_ne_zero.mp hr)] at hpos
      have hApos : 0 < A σ := by
        rcases le_or_gt (A σ) 0 with h1 | h1
        · rw [max_eq_right h1] at hmax; exact absurd hmax (lt_irrefl 0)
        · exact h1
      rw [max_eq_left hApos.le] at hle
      calc Real.log (gramDet h' σ s) ≤
            Real.log ((A σ ^ 2) ^ Module.finrank (𝓞 K) M.carrier * gramDet M.metric σ s) :=
            Real.log_le_log hg' hle
        _ = 2 * (Module.finrank (𝓞 K) M.carrier : ℝ) * Real.log (A σ) + Real.log (gramDet M.metric σ s) := by
          rw [Real.log_mul (by positivity) hg.ne', ← pow_mul, Real.log_pow]
          push_cast; ring
  simp only [HermitianBundle.deg, HermitianBundle.arithDegree]
  rw [arithDegree_eq M.metric hs (Fintype.card_fin _), arithDegree_eq h' hs (Fintype.card_fin _)]
  simp only [degreeWith]
  rw [← sub_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hsum : ∑ σ : K →+* ℂ, Real.log (gramDet h' σ s) ≤
      2 * (Module.finrank (𝓞 K) M.carrier : ℝ) * ∑ σ : K →+* ℂ, Real.log (A σ) + ∑ σ : K →+* ℂ, Real.log (gramDet M.metric σ s) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun σ _ ↦ hlog σ
  linarith

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
