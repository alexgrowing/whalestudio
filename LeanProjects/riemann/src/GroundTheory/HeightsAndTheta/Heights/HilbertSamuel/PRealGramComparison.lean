import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRealGramComparison
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFSExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionSup
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResSymGram
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.DetIneq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStB
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanDerivSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace RealGramComparison

open MvPolynomial MeasureTheory Filter Asymptotics Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder ComplexConjugate Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def dVGram (d : HSMDatum D Ω κ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    Matrix (Fin r) (Fin r) ℂ :=
  bGram d.dV (fun k y => secFun (b k) (resPt d y)) fun y => wgt d.m n (resPt d y)

theorem pairVal_eq (m : ConeMetric ℂ (Ix κ)) (n : ℕ) (b b' : MvPolynomial (Ix κ) ℚ) (z : Ix κ → ℂ) :
    pairVal m n b b' z = starRingEnd ℂ (secFun b' z) * secFun b z * (wgt m n z : ℂ) := by
  simp only [pairVal, secFun, wgt, div_eq_mul_inv]
  push_cast
  ring

theorem resCGram_eq (d : HSMDatum D Ω κ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    resCGram d n b = (dVGram d n b).transpose := by
  ext k l
  simp only [resCGram, dVGram, bGram, Matrix.transpose_apply, Matrix.of_apply, pairVal_eq]

theorem integrable_dV (d : HSMDatum D Ω κ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (i j : Fin r) :
    Integrable (fun y => starRingEnd ℂ (secFun (b i) (resPt d y)) * secFun (b j) (resPt d y) *
      (wgt d.m n (resPt d y) : ℂ)) d.dV := by
  have := d.vol.1
  have hc := ResSym.continuous_degZero_resPt d (ResSym.continuousOn_gramFun d.smooth n (b i) (b j))
    fun c z hc => ResSym.gramFun_smul (hb i) (hb j) c z hc
  exact integrableOn_univ.1 (hc.continuousOn.integrableOn_compact isCompact_univ)

theorem quad_bGram {X : Type*} [MeasurableSpace X] (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ) (c : Fin r → ℂ) :
    (star c ⬝ᵥ (bGram μ s w *ᵥ c)).re = bNormSq μ s w c := by
  rw [dot_bGram μ s w hint c, Complex.ofReal_re]

theorem isHermitian_ofReal_smul {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.IsHermitian) (t : ℝ) :
    ((t : ℂ) • A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hA.eq, Complex.star_def, Complex.conj_ofReal]

theorem re_det_ofReal_smul {r : ℕ} (t : ℝ) (A : Matrix (Fin r) (Fin r) ℂ) :
    ((t : ℂ) • A).det.re = t ^ r * A.det.re := by
  rw [Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem re_det_le_of_quad {r : ℕ} {A B : Matrix (Fin r) (Fin r) ℂ} (hA : A.PosSemidef) (hB : B.IsHermitian)
    (t : ℝ) (h : ∀ c : Fin r → ℂ, (star c ⬝ᵥ (A *ᵥ c)).re ≤ t * (star c ⬝ᵥ (B *ᵥ c)).re) :
    A.det.re ≤ t ^ r * B.det.re := by
  have hsub := psd_sub_of_quad_le (isHermitian_ofReal_smul hB t) hA.isHermitian fun c => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
    exact h c
  have := GroundTheory.Heights₂.Heights.MCDet.re_det_mono hA hsub
  simp only [RCLike.re_to_complex] at this
  rwa [re_det_ofReal_smul] at this

theorem abs_sub_le (hR : ResolutionSupBound.Statement) (d : HSMDatum D Ω κ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      |resChi d n - resCChi d n| ≤
        (finrank ℤ (sec ℤ d.x n) : ℝ) * (Real.log 2 + Real.log K + D * Real.log n) := by
  classical
  obtain ⟨C, hC⟩ := hR D Ω κ d
  refine ⟨max (C ^ 2) 1, le_max_right _ _, fun n hn => ?_⟩
  set K := max (C ^ 2) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogK := Real.log_nonneg hK1
  have hlogn := Real.log_nonneg hn1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL : 0 ≤ Real.log 2 + Real.log K + D * Real.log n := by positivity
  by_cases h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2
  swap
  · simp only [resChi, resCChi, dif_neg h, sub_zero, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hL
  rw [ResSym.resChi_eq d n h]
  simp only [resCChi, dif_pos h]
  have hp := h.choose_spec
  generalize h.choose = p at hp ⊢
  obtain ⟨r, b⟩ := p
  have hb : IsSecBasis d.x n b := hp
  have hrk : (r : ℝ) = finrank ℤ (sec ℤ d.x n) := by exact_mod_cast hb.card_eq
  rw [resCGram_eq, Matrix.det_transpose, ← hrk]
  have hintG := integrable_dV d hb.1
  have hintH := ResSym.integrable_gram d hb.1
  have key : ∀ c : Fin r → ℂ,
      bNormSq d.dV (fun k y => secFun (b k) (resPt d y)) (fun y => wgt d.m n (resPt d y)) c ≤
        2 * bNormSq (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c ∧
      bNormSq (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c ≤
        K * (n : ℝ) ^ D *
          bNormSq d.dV (fun k y => secFun (b k) (resPt d y)) (fun y => wgt d.m n (resPt d y)) c := by
    intro c
    have := d.vol.1
    set g : (Ix κ → ℂ) → ℝ := fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt d.m n z with hg
    have hnn : ∀ z, 0 ≤ g z := fun z =>
      mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg (d.m.nonneg z) _))
    have hcont : ContinuousOn g {0}ᶜ := continuousOn_normSq d.smooth b c
    have hdeg : ∀ (a : ℂ) z, a ≠ 0 → g (a • z) = g z := fun a z ha => isDegZero_normSq hb.1 c a z ha
    have eG : bNormSq d.dV (fun k y => secFun (b k) (resPt d y)) (fun y => wgt d.m n (resPt d y)) c =
        ∫ y, g (resPt d y) ∂d.dV := rfl
    have eH : bNormSq (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c =
        2⁻¹ * ((∫ y, g (resPt d y) ∂d.dV) + ∫ y, g (conjPt (resPt d y)) ∂d.dV) := by
      rw [← smul_eq_mul, ← ResSym.integral_symMeasure d hcont hdeg]
      rfl
    have hA : 0 ≤ ∫ y, g (resPt d y) ∂d.dV := integral_nonneg fun y => hnn _
    have hB : 0 ≤ ∫ y, g (conjPt (resPt d y)) ∂d.dV := integral_nonneg fun y => hnn _
    refine ⟨by rw [eG, eH]; linarith, ?_⟩

    set f : MvPolynomial (Ix κ) ℂ := ∑ k, MvPolynomial.C (c k) * map (algebraMap ℚ ℂ) (b k) with hf
    have hfh : f.IsHomogeneous n := by
      refine MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_
      obtain ⟨g', hg', hgb⟩ := hb.1 k
      rw [hgb, MvPolynomial.map_map]
      exact (hg'.map _).C_mul _
    have hevf : ∀ w, eval w f = ∑ i, c i * secFun (b i) w := by
      intro w
      simp [hf, secFun, map_sum]
    have hpt : ∀ w : Ix κ → ℂ, w ≠ 0 → ptNorm d.m (RingHom.id ℂ) n f w ^ 2 = g w := by
      intro w hw
      rw [ptNorm, MvPolynomial.map_id, hevf]
      simp only [hg, wgt]
      rw [div_pow, ← pow_mul, mul_comm n 2, div_eq_mul_inv]
    have hL2 : resolutionVolumeL2Complex d n f ^ 2 = ∫ y, g (resPt d y) ∂d.dV := by
      rw [resolutionVolumeL2Complex, Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)]
      exact integral_congr_ae (Eventually.of_forall fun y => hpt _ (ResSym.resPt_mem_pts d y).1)
    have hpow : ((n : ℝ) ^ ((D : ℝ) / 2)) ^ 2 = (n : ℝ) ^ D := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n),
        show (D : ℝ) / 2 * ((2 : ℕ) : ℝ) = (D : ℝ) by push_cast; ring, Real.rpow_natCast]
    set S := K * (n : ℝ) ^ D * ∫ y, g (resPt d y) ∂d.dV with hS
    have hsup : ∀ z ∈ pts (coordIdeal ℤ d.x), g z ≤ S := by
      intro z hz
      have h1 := hC n hn f hfh z hz
      have h0 : 0 ≤ ptNorm d.m (RingHom.id ℂ) n f z :=
        div_nonneg (norm_nonneg _) (pow_nonneg (d.m.nonneg z) _)
      have h2 := pow_le_pow_left₀ h0 h1 2
      rw [hpt z hz.1] at h2
      calc g z ≤ (C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f) ^ 2 := h2
        _ = C ^ 2 * (n : ℝ) ^ D * ∫ y, g (resPt d y) ∂d.dV := by rw [mul_pow, mul_pow, hpow, hL2]
        _ ≤ S := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hA
    have hi1 : Integrable (fun y => g (resPt d y)) d.dV :=
      integrableOn_univ.1 ((ResSym.continuous_degZero_resPt d hcont hdeg).continuousOn.integrableOn_compact
        isCompact_univ)
    have hi2 : Integrable (fun y => g (conjPt (resPt d y))) d.dV :=
      integrableOn_univ.1 ((ResSym.continuous_degZero_conj_resPt d hcont hdeg).continuousOn.integrableOn_compact
        isCompact_univ)
    have hS1 : ∫ y, g (resPt d y) ∂d.dV ≤ S := by
      have := integral_mono hi1 (integrable_const S) fun y => hsup _ (ResSym.resPt_mem_pts d y)
      simpa using this
    have hS2 : ∫ y, g (conjPt (resPt d y)) ∂d.dV ≤ S := by
      have := integral_mono hi2 (integrable_const S) fun y =>
        hsup _ (ResSym.conjPt_mem_pts (ResSym.resPt_mem_pts d y))
      simpa using this
    rw [eH, eG]
    rw [hS] at hS1 hS2
    linarith
  have hGpsd : (dVGram d n b).PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (bGram_isHermitian _ _ _) fun c => by
      rw [dVGram, dot_bGram _ _ _ hintG c]
      exact Complex.zero_le_real.mpr (integral_nonneg fun y =>
        mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg (d.m.nonneg _) _)))
  have hHpd := ResSym.posDef_gram d hb
  have d1 := re_det_le_of_quad hGpsd (bGram_isHermitian (ResSym.symMeasure d) (fun k => secFun (b k))
    (wgt d.m n)) 2 fun c => by
      rw [dVGram, quad_bGram _ _ _ hintG, quad_bGram _ _ _ hintH]
      exact (key c).1
  have d2 := re_det_le_of_quad hHpd.posSemidef (bGram_isHermitian d.dV
    (fun k y => secFun (b k) (resPt d y)) fun y => wgt d.m n (resPt d y)) (K * (n : ℝ) ^ D) fun c => by
      rw [quad_bGram _ _ _ hintG, quad_bGram _ _ _ hintH]
      exact (key c).2
  rw [← dVGram] at d2
  set G := dVGram d n b with hG
  set H := bGram (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n) with hH
  have hHpos : 0 < H.det.re := by
    have := GroundTheory.Heights₂.Heights.MCDet.re_det_pos hHpd
    simpa using this
  have hKn : 0 < K * (n : ℝ) ^ D := by positivity
  have hGpos : 0 < G.det.re := by
    by_contra hle
    push Not at hle
    have : (K * (n : ℝ) ^ D) ^ r * G.det.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
    linarith
  have l1 : Real.log G.det.re ≤ r * Real.log 2 + Real.log H.det.re := by
    have := Real.log_le_log hGpos d1
    rwa [Real.log_mul (by positivity) hHpos.ne', Real.log_pow] at this
  have l2 : Real.log H.det.re ≤ r * (Real.log K + D * Real.log n) + Real.log G.det.re := by
    have := Real.log_le_log hHpos d2
    rwa [Real.log_mul (by positivity) hGpos.ne', Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at this
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have a1 := mul_nonneg hr0 hlog2
  have a2 := mul_nonneg hr0 (add_nonneg hlogK (mul_nonneg (Nat.cast_nonneg D) hlogn))
  rw [abs_le]
  constructor <;> nlinarith

theorem rank_le (hP : ProjectionBounds.Statement) (hF : PullFSExtension.Statement) (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ) (hfr : IsProjFrame d.x e) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, (finrank ℤ (sec ℤ d.x n) : ℝ) ≤ A * ((n : ℝ) + 1) ^ D := by
  obtain ⟨m₀, hs, hc, hp, hpull⟩ := hF D Ω κ d.x e hfr
  obtain ⟨k, E, C, -, -, -, -, hrank, -⟩ := hP D Ω κ (d.withMetric m₀ ⊥ hs hc bot_le hp) e hfr hpull
  refine ⟨(projDeg d.x e : ℝ) / D.factorial + |C|, by positivity, fun n => ?_⟩
  have h1 : (finrank ℤ (sec ℤ d.x n) : ℝ) - (projDeg d.x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤
      C * ((n : ℝ) + 1) ^ (D - 1) := (abs_le.mp (hrank n)).2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n + 1 := by linarith
  have h2 : (n : ℝ) ^ D ≤ ((n : ℝ) + 1) ^ D := pow_le_pow_left₀ hn0 (by linarith) D
  have h3 : ((n : ℝ) + 1) ^ (D - 1) ≤ ((n : ℝ) + 1) ^ D := pow_le_pow_right₀ hn1 (Nat.sub_le D 1)
  have h4 : C * ((n : ℝ) + 1) ^ (D - 1) ≤ |C| * ((n : ℝ) + 1) ^ D :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h3 (abs_nonneg C))
  have h5 : (projDeg d.x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤
      (projDeg d.x e : ℝ) / D.factorial * ((n : ℝ) + 1) ^ D := by
    rw [div_mul_eq_mul_div]
    gcongr
  rw [add_mul]
  linarith

theorem proof (hR : ResolutionSupBound.Statement) (hP : ProjectionBounds.Statement)
    (hF : PullFSExtension.Statement) : RealGramComparison.Statement := by
  intro D Ω _ _ κ _ d e hfr
  obtain ⟨K, hK1, hK⟩ := abs_sub_le hR d
  obtain ⟨A, hA0, hA⟩ := rank_le hP hF d e hfr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK := Real.log_nonneg hK1
  set B := (Real.log 2 + Real.log K) / Real.log 2 + D with hB
  have hB0 : 0 ≤ B := by positivity
  refine IsBigO.of_bound (A * 2 ^ D * B) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn0 := Real.log_nonneg hn1
  have hlog21 : Real.log 2 ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hlogn : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  have hlog1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hL : Real.log 2 + Real.log K + D * Real.log n ≤ B * Real.log ((n : ℝ) + 1) := by
    have h1 : Real.log 2 + Real.log K ≤ (Real.log 2 + Real.log K) / Real.log 2 * Real.log ((n : ℝ) + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith
    have h2 : (D : ℝ) * Real.log n ≤ D * Real.log ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hlogn (Nat.cast_nonneg _)
    rw [hB, add_mul]
    linarith
  have hL0 : 0 ≤ Real.log 2 + Real.log K + D * Real.log n := by positivity
  have hpow : ((n : ℝ) + 1) ^ D ≤ 2 ^ D * (n : ℝ) ^ D := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) D
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1))]
  calc |resChi d n - resCChi d n|
      ≤ (finrank ℤ (sec ℤ d.x n) : ℝ) * (Real.log 2 + Real.log K + D * Real.log n) := hK n hn
    _ ≤ (A * ((n : ℝ) + 1) ^ D) * (B * Real.log ((n : ℝ) + 1)) :=
        mul_le_mul (hA n) hL hL0 (by positivity)
    _ ≤ (A * (2 ^ D * (n : ℝ) ^ D)) * (B * Real.log ((n : ℝ) + 1)) := by
        gcongr
    _ = A * 2 ^ D * B * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by ring

end

end RealGramComparison

end GroundTheory.Heights₂.Heights.HilbertSamuel
