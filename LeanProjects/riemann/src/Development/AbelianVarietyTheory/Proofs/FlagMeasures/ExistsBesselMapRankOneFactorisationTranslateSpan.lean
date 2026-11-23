import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetNotGG
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalStandardSideStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContinuousBesselMapSmoothVectorsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormIdentityBesselCoefficientQuotientStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.BeRankOne

theorem exists_rankOne_of_hermitian_nonneg_operatorKernel {H Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    (V : Set H) (B : H → H → (Wp →L[ℂ] Wp)) (l₀ : H → Wp)
    (hc : ∀ v ∈ V, ∀ ξ : Wp, ∃ c : ℂ, ∀ u ∈ V, B u v ξ = c • l₀ u)
    (hadj : ∀ u ∈ V, ∀ v ∈ V, ContinuousLinearMap.adjoint (B u v) = B v u)
    (hpos : ∀ v ∈ V, ∀ ξ : Wp, 0 ≤ (⟪ξ, B v v ξ⟫_ℂ).re ∧ (⟪ξ, B v v ξ⟫_ℂ).im = 0)
    (hne : ∃ u ∈ V, ∃ v ∈ V, ∃ ξ : Wp, B u v ξ ≠ 0) :
    ∃ t : ℂ, (∃ u ∈ V, t • l₀ u ≠ 0) ∧ ∀ u ∈ V, ∀ v ∈ V, B u v = rk1 (t • l₀ u) (t • l₀ v) := by
  classical
  obtain ⟨u₁, hu₁, v₁, hv₁, ξ₁, hne₁⟩ := hne
  choose! cf hcf using hc

  have hadj' : ∀ u ∈ V, ∀ v ∈ V, ∀ ξ η : Wp, ⟪η, B u v ξ⟫_ℂ = ⟪B v u η, ξ⟫_ℂ := by
    intro u hu v hv ξ η
    rw [← hadj u hu v hv, ContinuousLinearMap.adjoint_inner_left]

  obtain ⟨u₀, hu₀, hl₀⟩ : ∃ u₀ ∈ V, l₀ u₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hne₁ (by rw [hcf v₁ hv₁ ξ₁ u₁ hu₁, h u₁ hu₁, smul_zero])
  have hnpos : 0 < ‖l₀ u₀‖ ^ 2 := pow_pos (norm_pos_iff.mpr hl₀) 2
  have hN0 : ((‖l₀ u₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hself : ⟪l₀ u₀, l₀ u₀⟫_ℂ = ((‖l₀ u₀‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl

  obtain ⟨lam, hcol⟩ : ∃ lam : ℂ, ∀ v ∈ V, ∀ ξ : Wp, cf v ξ = lam * ⟪l₀ v, ξ⟫_ℂ := by
    refine ⟨starRingEnd ℂ (cf u₀ (l₀ u₀)) / ((‖l₀ u₀‖ ^ 2 : ℝ) : ℂ), fun v hv ξ => ?_⟩
    have h := hadj' u₀ hu₀ v hv ξ (l₀ u₀)
    rw [hcf v hv ξ u₀ hu₀, hcf u₀ hu₀ (l₀ u₀) v hv, inner_smul_right, inner_smul_left, hself] at h
    rw [div_mul_eq_mul_div, eq_div_iff hN0, mul_comm (cf v ξ)]
    rw [mul_comm] at h
    exact h
  have hB : ∀ u ∈ V, ∀ v ∈ V, ∀ ξ : Wp, B u v ξ = (lam * ⟪l₀ v, ξ⟫_ℂ) • l₀ u := by
    intro u hu v hv ξ
    rw [hcf v hv ξ u hu, hcol v hv ξ]

  have hq := hpos u₀ hu₀ (l₀ u₀)
  have he : ⟪l₀ u₀, B u₀ u₀ (l₀ u₀)⟫_ℂ = lam * (((‖l₀ u₀‖ ^ 2) * (‖l₀ u₀‖ ^ 2) : ℝ) : ℂ) := by
    rw [hB u₀ hu₀ u₀ hu₀, inner_smul_right, hself]
    push_cast
    ring
  rw [he, Complex.re_mul_ofReal, Complex.im_mul_ofReal] at hq
  have hmm : 0 < ‖l₀ u₀‖ ^ 2 * ‖l₀ u₀‖ ^ 2 := mul_pos hnpos hnpos
  have him : lam.im = 0 := (mul_eq_zero.mp hq.2).resolve_right hmm.ne'
  have hre : 0 ≤ lam.re := by
    by_contra h
    push Not at h
    linarith [mul_neg_of_neg_of_pos h hmm, hq.1]
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hne₁
    rw [hB u₁ hu₁ v₁ hv₁ ξ₁, h0, zero_mul, zero_smul]
  have hrepos : 0 < lam.re := by
    refine lt_of_le_of_ne hre (fun h => hlam0 ?_)
    exact Complex.ext (by simpa using h.symm) (by simpa using him)

  refine ⟨((Real.sqrt lam.re : ℝ) : ℂ), ⟨u₀, hu₀, smul_ne_zero ?_ hl₀⟩, fun u hu v hv => ?_⟩
  · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hrepos)
  have ht : starRingEnd ℂ ((Real.sqrt lam.re : ℝ) : ℂ) * ((Real.sqrt lam.re : ℝ) : ℂ) = lam := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hre]
    exact Complex.ext (by simp) (by simp [him])
  ext η
  rw [hB u hu v hv η, rankOneInnerOperator_apply, inner_smul_left, smul_smul]
  congr 1
  rw [mul_right_comm, ht]

theorem isBesselMapSm_smul {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ}
    {ψ : Mat k r → ℂ} {σ : Mat k r → (H →L[ℂ] H)} {π : Mat k r → (Wp →L[ℂ] Wp)} {l : H → Wp}
    (hl : IsBesselMapSm z ψ σ π l) (t : ℂ) : IsBesselMapSm z ψ σ π (fun u => t • l u) := by
  unfold Formalism.MainNotions.S.IsBesselMapSm Formalism.MainNotions.S.IsCWCont at *
  obtain ⟨hadd, hsm, heq, C, Ws, hWs, hb⟩ := hl
  refine ⟨?_, ?_, ?_, ‖t‖ * C, Ws, hWs, ?_⟩
  · intro v hv w hw
    show t • l (v + w) = t • l v + t • l w
    rw [hadd v hv w hw, smul_add]
  · intro c v hv
    show t • l (c • v) = c • (t • l v)
    rw [hsm c v hv, smul_comm]
  · intro h hh m hm v hv
    show t • l (σ (h * m) v) = ψ m • π h (t • l v)
    rw [heq h hh m hm v hv, map_smul, smul_comm]
  · intro v hv
    show ‖t • l v‖ ≤ _
    rw [norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb v hv) (norm_nonneg t)

end GlobalTheory.SgInf.BeRankOne

theorem GlobalTheory.SgInf.exists_isEll_DD : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → IsSmoothVec σ w → MultOne z (psiGen k r z c) σ π → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → NonVan z (psiGen k r z c) σ π w μG ν → ∃ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ w) l := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide hsm hM1 ν hq hNV
  obtain ⟨-, hU, -, -, hHG, -, -, hDec, -⟩ := id hStd
  obtain ⟨-, -, -, hHS, -⟩ := id hSide
  obtain ⟨hinv, -, hDV, -, hVsm⟩ := GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hU
  have hsmDD : ∀ v ∈ DD σ w, v ∈ smoothVecs (k := k) (r := r) σ :=
    fun v hv => (hVsm hsm).1 v (hDV hv)
  have hae := GlobalTheory.SgInf.WUnfold.ae_mem_GG hHG hHS hq

  have hne : ∃ u ∈ (DD σ w : Set H), ∃ v ∈ (DD σ w : Set H), ∃ ξ : Wp,
      be (psiGen k r z c) π μS σ u v ξ ≠ 0 := by
    by_contra hz
    push Not at hz
    obtain ⟨W, hWG, hWν, hWeq, hWfin, hWne, hWfix⟩ := hNV
    have hW0 : ∀ y ∈ GG k r, W y = 0 := by
      intro y hy
      rw [← hWfix y hy,
        (GlobalTheory.T.bessel_functional_standard_side k r σ w a μG d z c π μS hStd hSide ν hq W hWG hWν hWeq hWfin y hy).2,
        integral_eq_zero_of_ae, smul_zero]
      filter_upwards [hae] with g hg
      exact hz _ (mem_DD σ w hy) _ (mem_DD σ w hg) _
    apply hWne
    show (∫⁻ x, (‖W (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂ν) = 0
    rw [lintegral_congr_ae (g := fun _ => 0) ?_, lintegral_zero]
    filter_upwards [hae] with x hx
    simp [hW0 _ hx]
  obtain ⟨u₁, hu₁, v₁, hv₁, ξ₁, hne₁⟩ := hne
  obtain ⟨l₀, hB₀, hl₀⟩ := GlobalTheory.T.exists_continuous_besselMap_smoothVectors k r σ w a μG d z c π μS hStd hSide hsm v₁ hv₁ ξ₁

  have hcol : ∀ v ∈ (DD σ w : Set H), ∀ ξ : Wp, ∃ b : ℂ, ∀ u ∈ (DD σ w : Set H),
      be (psiGen k r z c) π μS σ u v ξ = b • l₀ u := by
    intro v hv ξ
    obtain ⟨l, hB, hl⟩ := GlobalTheory.T.exists_continuous_besselMap_smoothVectors k r σ w a μG d z c π μS hStd hSide hsm v hv ξ
    obtain ⟨b, hb | hb⟩ := hM1 l l₀ hB hB₀
    · exact ⟨b, fun u hu => by rw [← hl u hu]; exact hb u (hsmDD u hu)⟩
    · have hb0 : b ≠ 0 := by
        rintro rfl
        apply hne₁
        rw [← hl₀ u₁ hu₁, hb u₁ (hsmDD u₁ hu₁), zero_smul]
      refine ⟨b⁻¹, fun u hu => ?_⟩
      rw [← hl u hu, hb u (hsmDD u hu), inv_smul_smul₀ hb0]
  obtain ⟨t, ⟨u₂, hu₂, hne₂⟩, hrk⟩ := GlobalTheory.SgInf.BeRankOne.exists_rankOne_of_hermitian_nonneg_operatorKernel (DD σ w : Set H)
    (be (psiGen k r z c) π μS σ) l₀ hcol
    (fun u hu v hv =>
      (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H) hinv hDec u hu v hv).2.2.1)
    (fun v hv ξ => by
      have h := GlobalTheory.T.norm_identity_besselCoefficient_quotient k r σ w a μG d z c π μS hStd hSide ν hq v hv v hv v hv ξ
      exact ⟨h.2.2.2.2.1, h.2.2.2.2.2⟩)
    ⟨u₁, hu₁, v₁, hv₁, ξ₁, hne₁⟩
  refine ⟨fun u => t • l₀ u, ?_⟩
  unfold GlobalTheory.SgInf.IsEll
  exact ⟨GlobalTheory.SgInf.BeRankOne.isBesselMapSm_smul hB₀ t, ⟨u₂, hu₂, hne₂⟩, hrk⟩
