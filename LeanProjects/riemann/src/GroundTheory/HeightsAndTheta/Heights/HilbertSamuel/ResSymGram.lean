import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ResSymMeasure
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionSup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ResSym

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.AnForm.M
open scoped ENNReal ComplexOrder

noncomputable section

set_option linter.unusedSectionVars false

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem gramFun_smul {m : ConeMetric ℂ (Ix κ)} {n : ℕ} {b b' : MvPolynomial (Ix κ) ℚ}
    (hb : ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b = map (Int.castRingHom ℚ) f)
    (hb' : ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b' = map (Int.castRingHom ℚ) f)
    (c : ℂ) (z : Ix κ → ℂ) (hc : c ≠ 0) :
    starRingEnd ℂ (secFun b (c • z)) * secFun b' (c • z) * (wgt m n (c • z) : ℂ) =
      starRingEnd ℂ (secFun b z) * secFun b' z * (wgt m n z : ℂ) := by
  rw [secFun_smul hb, secFun_smul hb', wgt, wgt, m.smul, map_mul, map_pow]
  have hc' : (‖c‖ : ℂ) ≠ 0 := by simpa using hc
  have hk : starRingEnd ℂ c ^ n * c ^ n = (‖c‖ : ℂ) ^ (2 * n) := by
    rw [← mul_pow, Complex.conj_mul', ← pow_mul]
  push_cast
  calc _ = (starRingEnd ℂ c ^ n * c ^ n) * ((‖c‖ : ℂ) ^ (2 * n))⁻¹ *
          (starRingEnd ℂ (secFun b z) * secFun b' z * ((m.ρ z : ℂ) ^ (2 * n))⁻¹) := by ring
    _ = _ := by
        rw [hk, mul_inv_cancel₀ (pow_ne_zero _ hc'), one_mul]

theorem continuousOn_gramFun {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) (n : ℕ)
    (b b' : MvPolynomial (Ix κ) ℚ) :
    ContinuousOn (fun z => starRingEnd ℂ (secFun b z) * secFun b' z * (wgt m n z : ℂ)) {0}ᶜ := by
  have hρ : ContinuousOn m.ρ {0}ᶜ := continuousOn_rho hm
  refine (((continuous_secFun _).continuousOn.star).mul (continuous_secFun _).continuousOn).mul
    (Complex.continuous_ofReal.comp_continuousOn ((hρ.pow _).inv₀ fun z hz => ?_))
  exact pow_ne_zero _ (m.pos z hz).ne'

theorem integrable_gram (d : HSMDatum D Ω κ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (i j : Fin r) :
    Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt d.m n z : ℂ))
      (symMeasure d) := by
  set h : (Ix κ → ℂ) → ℂ := fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt d.m n z : ℂ)
    with hh
  have hcont : ContinuousOn h {0}ᶜ := continuousOn_gramFun d.smooth n (b i) (b j)
  have hsm : ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 → h (c • z) = h z := fun c z hc =>
    gramFun_smul (hb i) (hb j) c z hc
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Ix κ → ℂ) 1).exists_bound_of_continuousOn
    (hcont.mono fun z hz => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      simp at hz)
  have hbd : ∀ z, ‖h z‖ ≤ max C ‖h 0‖ := by
    intro z
    by_cases hz : z = 0
    · rw [hz]; exact le_max_right _ _
    · have hz' : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
      have hu : ((‖z‖ : ℂ)⁻¹ • z) ∈ Metric.sphere (0 : Ix κ → ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
      have : z = (‖z‖ : ℂ) • ((‖z‖ : ℂ)⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ hz', one_smul]
      rw [this, hsm _ _ hz']
      exact (hC _ hu).trans (le_max_left _ _)
  exact Integrable.of_bound (measurable_of_continuousOn_compl_singleton 0 hcont).aestronglyMeasurable
    _ (Filter.Eventually.of_forall hbd)

theorem mem_mcPts_of_pts {x : Ix κ → Ω} {z : Ix κ → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ x) := by
  refine ⟨fun k => ?_, hz.2⟩
  obtain ⟨p, hp⟩ := Function.ne_iff.mp hz.1
  exact ⟨p.2, by cases k; exact hp⟩

theorem exists_form_J (d : HSMDatum D Ω κ) :
    ∃ (g : MvPolynomial (Ix κ) ℤ) (N : ℕ), g ∈ d.J ∧ g.IsHomogeneous N ∧ aeval d.x g ≠ 0 := by
  obtain ⟨S, hS, hJ⟩ := d.R.homog
  have : ¬ S ⊆ coordIdeal ℤ d.x := fun hsub => d.R.nondeg (by
    rw [hJ]; exact Ideal.span_le.mpr hsub)
  obtain ⟨g, hgS, hgP⟩ := Set.not_subset.mp this
  obtain ⟨a, ha⟩ := hS g hgS
  have hhom : g.IsHomogeneous (a ()) := by
    intro m hm
    have h := ha m (mem_support_iff.mpr hm) ()
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    simpa [Fintype.sum_sigma] using h
  refine ⟨g, a (), ?_, hhom, fun h0 => hgP (mem_coordIdeal_of_isHomogeneous ℤ d.x hhom h0)⟩
  rw [hJ]
  exact Ideal.subset_span hgS

theorem posDef_gram (d : HSMDatum D Ω κ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis d.x n b) : (bGram (symMeasure d) (fun k => secFun (b k)) (wgt d.m n)).PosDef := by
  classical
  have hint := integrable_gram d hb.1
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (bGram_isHermitian _ _ _) fun c hc => ?_
  rw [dot_bGram _ _ _ hint c, Complex.zero_lt_real]
  set h : (Ix κ → ℂ) → ℝ := fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt d.m n z with hh
  have hnn : ∀ z, 0 ≤ h z := fun z =>
    mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg (d.m.nonneg z) _))
  have hcont : ContinuousOn h {0}ᶜ := continuousOn_normSq d.smooth b c
  have hdeg : ∀ (a : ℂ) z, a ≠ 0 → h (a • z) = h z := fun a z ha => isDegZero_normSq hb.1 c a z ha
  change 0 < ∫ z, h z ∂(symMeasure d)
  rw [integral_symMeasure d hcont hdeg, smul_eq_mul]
  have hA : 0 ≤ ∫ y, h (resPt d y) ∂d.dV := integral_nonneg fun y => hnn _
  have hB : 0 ≤ ∫ y, h (conjPt (resPt d y)) ∂d.dV := integral_nonneg fun y => hnn _
  by_contra hle
  have hA0 : ∫ y, h (resPt d y) ∂d.dV = 0 := by
    push Not at hle
    nlinarith

  have := d.vol.1
  have hc1 := continuous_degZero_resPt d hcont hdeg
  have hi1 : Integrable (fun y => h (resPt d y)) d.dV :=
    integrableOn_univ.1 (hc1.continuousOn.integrableOn_compact isCompact_univ)
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => hnn _) hi1).mp hA0
  have hv : ∀ y, h (resPt d y) = 0 := by
    intro y₀
    by_contra hy₀
    have hO : IsOpen {y | h (resPt d y) ≠ 0} := isOpen_ne_fun hc1 continuous_const
    have hpos := dV_pos_of_isOpen d hO ⟨y₀, hy₀⟩
    exact hpos.ne' (ae_iff.mp hae)
  set F : (Ix κ → ℂ) → ℂ := fun z => ∑ i, c i * secFun (b i) z with hF
  have hFv : ∀ y, F (resPt d y) = 0 := by
    intro y
    have h1 := hv y
    have hw : 0 < wgt d.m n (resPt d y) := inv_pos.mpr (pow_pos (d.m.pos _ (resPt_mem_pts d y).1) _)
    have h2 : ‖F (resPt d y)‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h1 with h' | h'
      · exact h'
      · exact absurd h' hw.ne'
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)

  have hFpts : ∀ z ∈ pts (coordIdeal ℤ d.x), z ∉ mcPts (ι := GlobalTheory κ) d.J → F z = 0 := by
    intro z hz hzJ
    obtain ⟨y, hy⟩ := d.R.surj z (mem_mcPts_of_pts hz) hzJ
    obtain ⟨a, ha, he⟩ := sameOrbit_eq_smul hy
    have h1 : ∑ i, c i * secFun (b i) (a • z) = 0 := by
      have := hFv y
      change ∑ i, c i * secFun (b i) (d.R.lift y y) = 0 at this
      rwa [he] at this
    rw [sum_secFun_smul hb.1 c a z] at h1
    exact (mul_eq_zero.mp h1).resolve_left (pow_ne_zero _ ha)
  have hX : Nonempty d.R.X := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h1 : d.dV Set.univ = 1 := measure_univ
    rw [Set.univ_eq_empty_iff.mpr hne, measure_empty] at h1
    exact zero_ne_one h1
  obtain ⟨y₀⟩ := hX
  have hF0 : F 0 = 0 := by
    have h1 := sum_secFun_smul hb.1 c 0 (resPt d y₀)
    rw [zero_smul] at h1
    change F 0 = _ at h1
    have h2 := hFv y₀
    change ∑ i, c i * secFun (b i) (resPt d y₀) = 0 at h2
    rw [h1, h2, mul_zero]

  obtain ⟨g, N, hgJ, -, hgx⟩ := exists_form_J d
  set b' : Fin r → MvPolynomial (Ix κ) ℚ := fun k => b k * map (Int.castRingHom ℚ) g with hb'
  have hli : LinearIndependent ℚ fun k => aeval d.x (b' k) := by
    have hs := linIndep_rat_of_isSecBasis hb
    rw [linearIndependent_iff'] at hs ⊢
    intro s w hsum i hi
    refine hs s w ?_ i hi
    have h1 : (∑ i ∈ s, w i • aeval d.x (b i)) * aeval d.x g = 0 := by
      rw [Finset.sum_mul, ← hsum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_mul_assoc]
      simp only [hb', map_mul, aeval_map_intQ]
    exact (mul_eq_zero.mp h1).resolve_right hgx
  refine hc (coeff_eq_zero_of_vanish hli fun z hz => ?_)
  have hsum : ∑ k, c k * secFun (b' k) z = F z * eval z (map (Int.castRingHom ℂ) g) := by
    rw [hF, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hb', secFun, map_mul]
    rw [show (map (algebraMap ℚ ℂ)) ((map (Int.castRingHom ℚ)) g) = map (Int.castRingHom ℂ) g by
      rw [MvPolynomial.map_map]; congr 1; try exact RingHom.ext_int _ _]
    try ring
  rw [hsum]
  by_cases hz0 : z = 0
  · rw [hz0, hF0, zero_mul]
  · have hzp : z ∈ pts (coordIdeal ℤ d.x) := ⟨hz0, hz⟩
    by_cases hzJ : z ∈ mcPts (ι := GlobalTheory κ) d.J
    · rw [hzJ.2 g hgJ, mul_zero]
    · rw [hFpts z hzp hzJ, zero_mul]

theorem sup_le_gram (hR : ResolutionSupBound.Statement) (d : HSMDatum D Ω κ) :
    ∃ K : ℝ, ∀ (n r : ℕ) (b : Fin r → MvPolynomial (Ix κ) ℚ), 1 ≤ n → IsSecBasis d.x n b →
      ∀ (c : Fin r → ℂ), ∀ z ∈ pts (coordIdeal ℤ d.x),
        ‖∑ k, c k * secFun (b k) z‖ ^ 2 * wgt d.m n z ≤
          K * (n : ℝ) ^ D * bNormSq (symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c := by
  classical
  obtain ⟨C, hC⟩ := hR D Ω κ d
  refine ⟨2 * C ^ 2, fun n r b hn hb c z hz => ?_⟩
  set f : MvPolynomial (Ix κ) ℂ := ∑ k, MvPolynomial.C (c k) * map (algebraMap ℚ ℂ) (b k) with hf
  have hfh : f.IsHomogeneous n := by
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_
    obtain ⟨g, hg, hgb⟩ := hb.1 k
    rw [hgb, MvPolynomial.map_map]
    exact (hg.map _).C_mul _
  set h : (Ix κ → ℂ) → ℝ := fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt d.m n z with hh
  have hnn : ∀ z, 0 ≤ h z := fun z =>
    mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg (d.m.nonneg z) _))
  have hcont : ContinuousOn h {0}ᶜ := continuousOn_normSq d.smooth b c
  have hdeg : ∀ (a : ℂ) z, a ≠ 0 → h (a • z) = h z := fun a z ha => isDegZero_normSq hb.1 c a z ha
  have hevf : ∀ w, eval w f = ∑ i, c i * secFun (b i) w := by
    intro w
    simp [hf, secFun, map_sum]
  have hpt : ∀ w : Ix κ → ℂ, w ≠ 0 → ptNorm d.m (RingHom.id ℂ) n f w ^ 2 = h w := by
    intro w hw
    have hρ : 0 < d.m.ρ w := d.m.pos w hw
    rw [ptNorm, MvPolynomial.map_id, hevf]
    simp only [hh, wgt]
    rw [div_pow, ← pow_mul, mul_comm n 2, div_eq_mul_inv]

  have hL : resolutionVolumeL2Complex d n f ^ 2 ≤ 2 * bNormSq (symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c := by
    have hI : 0 ≤ ∫ y, ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2 ∂d.dV :=
      integral_nonneg fun y => sq_nonneg _
    rw [resolutionVolumeL2Complex, Real.sq_sqrt hI]
    have he : (fun y => ptNorm d.m (RingHom.id ℂ) n f (resPt d y) ^ 2) = fun y => h (resPt d y) := by
      funext y
      exact hpt _ (resPt_mem_pts d y).1
    have hbn : bNormSq (symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c = ∫ z, h z ∂(symMeasure d) := rfl
    rw [he, hbn, integral_symMeasure d hcont hdeg, smul_eq_mul]
    have hB : 0 ≤ ∫ y, h (conjPt (resPt d y)) ∂d.dV := integral_nonneg fun y => hnn _
    linarith
  have h1 := hC n hn f hfh z hz
  have h0 : 0 ≤ ptNorm d.m (RingHom.id ℂ) n f z :=
    div_nonneg (norm_nonneg _) (pow_nonneg (d.m.nonneg z) _)
  have h2 := pow_le_pow_left₀ h0 h1 2
  rw [hpt z hz.1] at h2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hpow : ((n : ℝ) ^ ((D : ℝ) / 2)) ^ 2 = (n : ℝ) ^ D := by
    rw [← Real.rpow_mul_natCast hn0, show (D : ℝ) / 2 * ((2 : ℕ) : ℝ) = (D : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  calc h z ≤ (C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f) ^ 2 := h2
    _ = C ^ 2 * (n : ℝ) ^ D * resolutionVolumeL2Complex d n f ^ 2 := by rw [mul_pow, mul_pow, hpow]
    _ ≤ C ^ 2 * (n : ℝ) ^ D * (2 * bNormSq (symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
    _ = _ := by ring

theorem pairVal_eq_conj (m : ConeMetric ℂ (Ix κ)) (n : ℕ) (b b' : MvPolynomial (Ix κ) ℚ) (z : Ix κ → ℂ) :
    pairVal m n b b' z = starRingEnd ℂ (starRingEnd ℂ (secFun b z) * secFun b' z * (wgt m n z : ℂ)) := by
  simp only [pairVal, secFun, wgt, map_mul, Complex.conj_conj, Complex.conj_ofReal, div_eq_mul_inv]
  push_cast
  ring

theorem det_resGram (d : HSMDatum D Ω κ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f) :
    (resGram d n b).det = (bGram (symMeasure d) (fun k => secFun (b k)) (wgt d.m n)).det.re := by
  have hG : bGram (symMeasure d) (fun k => secFun (b k)) (wgt d.m n) =
      Complex.ofRealHom.mapMatrix (resGram d n b) := by
    ext k l
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe]
    have hreal := conj_bGram d.conjInv (map_conjPt_symMeasure d) n b k l
    rw [← Complex.conj_eq_iff_re.mp hreal]
    congr 1
    simp only [bGram, Matrix.of_apply, resGram]
    rw [integral_symMeasure d (continuousOn_gramFun d.smooth n (b k) (b l))
      (fun c z hc => gramFun_smul (hb k) (hb l) c z hc)]
    simp only [pairVal_eq_conj]
    rw [integral_conj, integral_conj, Complex.conj_re, Complex.conj_re, Complex.real_smul,
      Complex.re_ofReal_mul, Complex.add_re]
    ring
  rw [hG, ← RingHom.map_det, Complex.ofRealHom_eq_coe, Complex.ofReal_re]

theorem resChi_eq (d : HSMDatum D Ω κ) (n : ℕ)
    (h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2) :
    resChi d n = -(1 / 2) * Real.log
      (bGram (symMeasure d) (fun k => secFun (h.choose.2 k)) (wgt d.m n)).det.re := by
  unfold resChi
  rw [dif_pos h, det_resGram d h.choose_spec.1]

end

end ResSym

end GroundTheory.Heights₂.Heights.HilbertSamuel
