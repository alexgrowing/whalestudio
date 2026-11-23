import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarPolA

noncomputable section

open Matrix Filter Topology MeasureTheory Metric
open scoped NNReal ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.HPol

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pmat_zero' (ε : Fin n → Bool) : pmat (0 : PCoord ε → ℂ) = 0 := by
  ext a b; simp [pmat]

theorem kMat_zero' (ε : Fin n → Bool) : kMat (0 : KCo ε) = 0 := by
  ext a b; simp [kMat]

theorem gMat_fst {ε : Fin n → Bool} (w : KCo ε) : gMat ((w, 0) : GCo ε) = kMat w := by
  simp [gMat, pmat_zero']

theorem gMat_snd {ε : Fin n → Bool} (z : PCoord ε → ℂ) : gMat ((0, z) : GCo ε) = pmat z := by
  simp [gMat, kMat_zero']

def gLin (ε : Fin n → Bool) : GCo ε →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := gMat
  map_add' s t := by
    ext a b
    simp only [gMat, kMat, pmat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    split_ifs <;> simp <;> ring
  map_smul' c s := by
    ext a b
    simp only [gMat, kMat, pmat, Matrix.add_apply, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp [Complex.real_smul] <;> ring

theorem inUJ_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) :
    inUJ ε (g * h) := by
  unfold inUJ at *
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [hg, hh]

theorem inUJ_pol {ε : Fin n → Bool} (s : GCo ε) :
    inUJ ε (NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)) := by
  rw [← gMat_fst, ← gMat_snd]
  exact inUJ_mul (exp_inUJ (inG_gMat _)) (exp_inUJ (inG_gMat _))

def Lm {ε : Fin n → Bool} (s : GCo ε) : GCo ε :=
  cLin ε (logM n (NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)))

section An

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_comp_strict {ε : Fin n → Bool} (A : GCo ε →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    HasStrictFDerivAt (fun s => NormedSpace.exp (A s)) A 0 := by
  have h1 : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _)
      (ContinuousLinearMap.id ℝ _) (A 0) := by
    rw [map_zero]; exact exp_strict
  exact h1.comp (0 : GCo ε) A.hasStrictFDerivAt

theorem prod_strict (ε : Fin n → Bool) :
    HasStrictFDerivAt (fun s : GCo ε => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2))
      (LinearMap.toContinuousLinearMap (gLin ε)) 0 := by
  let kL : GCo ε →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap ((gLin ε).comp ((LinearMap.inl ℝ _ _).comp (LinearMap.fst ℝ _ _)))
  let pL : GCo ε →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap ((gLin ε).comp ((LinearMap.inr ℝ _ _).comp (LinearMap.snd ℝ _ _)))
  have ek : ∀ s : GCo ε, kL s = kMat s.1 := fun s => gMat_fst s.1
  have ep : ∀ s : GCo ε, pL s = pmat s.2 := fun s => gMat_snd s.2
  have h := (exp_comp_strict kL).mul' (exp_comp_strict pL)
  have hf : ((fun s : GCo ε => NormedSpace.exp (kL s)) * fun s => NormedSpace.exp (pL s)) =
      fun s => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2) := by
    funext s; rw [Pi.mul_apply, ek, ep]
  rw [hf] at h
  refine h.congr_fderiv (ContinuousLinearMap.ext fun s => ?_)
  have e0 : kMat (0 : GCo ε).1 = 0 := kMat_zero' ε
  have e1 : pmat (0 : GCo ε).2 = 0 := pmat_zero' ε
  change NormedSpace.exp (kL 0) * pL s + kL s * NormedSpace.exp (pL 0) = gMat s
  rw [ek, ep, ek, ep, e0, e1, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one, add_comm]
  rfl

theorem Lm_strict (ε : Fin n → Bool) :
    HasStrictFDerivAt (Lm (ε := ε)) (ContinuousLinearMap.id ℝ (GCo ε)) 0 := by
  have h0 : (fun s : GCo ε => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)) 0 = 1 := by
    simp [kMat_zero', pmat_zero']
  have hl : HasStrictFDerivAt (logM n) (ContinuousLinearMap.id ℝ _)
      ((fun s : GCo ε => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)) 0) := by
    rw [h0]; exact logM_strict
  have h := (LinearMap.toContinuousLinearMap (cLin ε)).hasStrictFDerivAt.comp (0 : GCo ε)
    (hl.comp (0 : GCo ε) (prod_strict ε))
  refine h.congr_fderiv (ContinuousLinearMap.ext fun s => ?_)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.id_apply,
    LinearMap.coe_toContinuousLinearMap']
  exact cLin_gMat s

end An

section An

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem Lm_exp (ε : Fin n → Bool) : ∀ᶠ s in 𝓝 (0 : GCo ε),
    NormedSpace.exp (gMat (Lm s)) = NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2) := by
  have hP0 : NormedSpace.exp (kMat (0 : GCo ε).1) * NormedSpace.exp (pmat (0 : GCo ε).2) = 1 := by
    simp [kMat_zero', pmat_zero']
  have hP : Tendsto (fun s : GCo ε => NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2))
      (𝓝 0) (𝓝 1) := by
    have := (prod_strict ε).continuousAt.tendsto
    rwa [hP0] at this
  have hl : Tendsto (logM n) (𝓝 1) (𝓝 0) := by
    have := (logM_strict (n := n)).continuousAt.tendsto
    rwa [logM_one] at this
  have hΦ := hl.comp hP
  have hc : Continuous fun Y : Matrix (Fin n) (Fin n) ℂ => Jm ε * (-Yᴴ) * Jm ε :=
    (continuous_const.matrix_mul continuous_id.matrix_conjTranspose.neg).matrix_mul continuous_const
  have hJ : Tendsto (fun s : GCo ε =>
      Jm ε * (-(logM n (NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)))ᴴ) * Jm ε)
      (𝓝 0) (𝓝 0) := by
    have := (hc.tendsto 0).comp hΦ
    simp only [Matrix.conjTranspose_zero, neg_zero, Matrix.mul_zero, Matrix.zero_mul] at this
    exact this
  filter_upwards [hP.eventually exp_logM, hΦ.eventually logM_exp, hJ.eventually logM_exp]
    with s h1 h2 h3
  have hU : inUJ ε (NormedSpace.exp (logM n (NormedSpace.exp (kMat s.1) * NormedSpace.exp (pmat s.2)))) := by
    rw [h1]; exact inUJ_pol s
  have hG := inG_of_exp (logM n) hU h2 h3
  show NormedSpace.exp (gMat (cLin ε _)) = _
  rw [gMat_cLin hG, h1]

end An

theorem polSet_eq_expSet (ε : Fin n → Bool) : ∃ δ > 0, ∀ S : Set (GCo ε), (∀ s ∈ S, ‖s‖ < δ) →
    polSet S = expSet (Lm '' S) := by
  obtain ⟨δ, hδ, h⟩ := Metric.eventually_nhds_iff_ball.mp (Lm_exp ε)
  refine ⟨δ, hδ, fun S hS => ?_⟩
  ext g
  constructor
  · rintro ⟨s, hs, hg⟩
    refine ⟨Lm s, ⟨s, hs, rfl⟩, ?_⟩
    rw [hg, h s (by simpa using hS s hs)]
  · rintro ⟨t, ⟨s, hs, rfl⟩, hg⟩
    refine ⟨s, hs, ?_⟩
    rw [hg, h s (by simpa using hS s hs)]

theorem Lm_zero (ε : Fin n → Bool) : Lm (0 : GCo ε) = 0 := by
  simp [Lm, kMat_zero', pmat_zero', logM_one]

instance borel_gco (ε : Fin n → Bool) : BorelSpace (GCo ε) := Prod.borelSpace

theorem volume_gco_isAddHaar (ε : Fin n → Bool) : (volume : Measure (GCo ε)).IsAddHaarMeasure := by
  have : (volume : Measure (KPair ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (PCoord ε → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (KCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact Measure.prod.instIsAddHaarMeasure _ _

theorem image_est (ε : Fin n → Bool) {η : ℝ} (hη : 0 < η) : ∃ δ > 0, ∀ S : Set (GCo ε),
    MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
      MeasurableSet (Lm '' S) ∧ (∀ s ∈ S, ‖Lm s‖ ≤ 2 * ‖s‖) ∧
      volume (Lm '' S) ≤ ENNReal.ofReal (1 + η) * volume S ∧
      ENNReal.ofReal (1 - η) * volume S ≤ volume (Lm '' S) := by
  have := volume_gco_isAddHaar ε
  set A := ContinuousLinearMap.id ℝ (GCo ε)
  have hdet : A.det = 1 := by
    rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_id, LinearMap.det_id]
  have hm1 : ENNReal.ofReal |A.det| < ((Real.toNNReal (1 + η) : ℝ≥0) : ℝ≥0∞) := by
    rw [hdet, abs_one, ENNReal.ofReal_one]
    have : (1 : ℝ≥0) < Real.toNNReal (1 + η) := by
      rw [← Real.toNNReal_one]; exact (Real.toNNReal_lt_toNNReal_iff (by linarith)).2 (by linarith)
    exact_mod_cast this
  have hm2 : ((Real.toNNReal (1 - η) : ℝ≥0) : ℝ≥0∞) < ENNReal.ofReal |A.det| := by
    rw [hdet, abs_one, ENNReal.ofReal_one]
    have : Real.toNNReal (1 - η) < 1 := by
      rw [Real.toNNReal_lt_one]; linarith
    exact_mod_cast this
  have h1 := addHaar_image_le_mul_of_det_lt (volume : Measure (GCo ε)) A hm1
  have h2 := mul_le_addHaar_image_of_lt_det (volume : Measure (GCo ε)) A hm2
  have h3 : ∀ᶠ c in 𝓝[>] (0 : ℝ≥0), c < 1 :=
    nhdsWithin_le_nhds (eventually_lt_nhds zero_lt_one)
  have h4 : ∀ᶠ c in 𝓝[>] (0 : ℝ≥0), 0 < c := self_mem_nhdsWithin
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ := (h1.and (h2.and (h3.and h4))).exists
  obtain ⟨U, hU, hA⟩ := (Lm_strict ε).approximates_deriv_on_nhds (c := c) (Or.inr hc4)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hB := hA.mono_set hball
  refine ⟨δ, hδ, fun S hS hSδ => ?_⟩
  have hSb : S ⊆ ball 0 δ := fun s hs => mem_ball_zero_iff.mpr (hSδ s hs)
  have hAS := hB.mono_set hSb
  have hc1' : (c : ℝ) < 1 := by exact_mod_cast hc3
  have hinj : Set.InjOn Lm S := by
    intro x hx y hy hxy
    have h := hAS x hx y hy
    simp only [A, ContinuousLinearMap.id_apply, hxy, sub_self, zero_sub, norm_neg] at h
    have h0 : ‖x - y‖ = 0 := by
      have := norm_nonneg (x - y)
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have : PolishSpace (KPair ε → ℂ) := inferInstance
  have : PolishSpace (PCoord ε → ℂ) := inferInstance
  have : PolishSpace (KCo ε) := inferInstance
  have : PolishSpace (GCo ε) := inferInstance
  refine ⟨hS.image_of_continuousOn_injOn hAS.continuousOn hinj, fun s hs => ?_, hc1 S Lm hAS,
    hc2 S Lm hAS⟩
  have h := hB s (hSb hs) 0 (mem_ball_self hδ)
  simp only [A, ContinuousLinearMap.id_apply, Lm_zero, sub_zero] at h
  have := norm_sub_norm_le (Lm s) s
  have := norm_nonneg s
  nlinarith

end ReciprocityTheory.ChartRestriction.DS.HPol
