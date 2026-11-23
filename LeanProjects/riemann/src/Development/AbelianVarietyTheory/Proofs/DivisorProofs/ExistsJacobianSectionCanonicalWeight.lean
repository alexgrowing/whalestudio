import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.JacSec

noncomputable section

def jacM {n : ℕ} (f0 : V n → ℂ) (f : Fin n → V n → ℂ) (v : V n) : V n →L[ℂ] V n :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm : (Fin n → ℂ) →L[ℂ] V n).comp
    (ContinuousLinearMap.pi fun k => f0 v • fderiv ℂ (f k) v - f k v • fderiv ℂ f0 v)

theorem jacM_apply {n : ℕ} (f0 : V n → ℂ) (f : Fin n → V n → ℂ) (v ξ : V n) (k : Fin n) :
    (jacM f0 f v ξ).ofLp k = f0 v * fderiv ℂ (f k) v ξ - f k v * fderiv ℂ f0 v ξ := by
  simp [jacM]

theorem jacM_congr {n : ℕ} {f0 g0 : V n → ℂ} {f g : Fin n → V n → ℂ} {v : V n}
    (h0 : f0 =ᶠ[𝓝 v] g0) (h : ∀ k, f k =ᶠ[𝓝 v] g k) : jacM f0 f v = jacM g0 g v := by
  ext ξ k
  rw [jacM_apply, jacM_apply, h0.fderiv_eq, (h k).fderiv_eq, h0.eq_of_nhds, (h k).eq_of_nhds]

theorem jacM_trans {n : ℕ} (G : V n → ℂ) (Φ : V n → V n) (h0 : V n → ℂ) (h : Fin n → V n → ℂ)
    (v : V n) (hG : DifferentiableAt ℂ G v) (hΦ : DifferentiableAt ℂ Φ v)
    (hh0 : DifferentiableAt ℂ h0 (Φ v)) (hh : ∀ k, DifferentiableAt ℂ (h k) (Φ v)) :
    jacM (fun w => G w * h0 (Φ w)) (fun k w => G w * h k (Φ w)) v =
      (G v ^ 2) • (jacM h0 h (Φ v)).comp (fderiv ℂ Φ v) := by
  have d0 : fderiv ℂ (fun w => G w * h0 (Φ w)) v =
      G v • ((fderiv ℂ h0 (Φ v)).comp (fderiv ℂ Φ v)) + h0 (Φ v) • fderiv ℂ G v :=
    (hG.hasFDerivAt.mul (hh0.hasFDerivAt.comp v hΦ.hasFDerivAt)).fderiv
  have dk : ∀ k, fderiv ℂ (fun w => G w * h k (Φ w)) v =
      G v • ((fderiv ℂ (h k) (Φ v)).comp (fderiv ℂ Φ v)) + h k (Φ v) • fderiv ℂ G v := fun k =>
    (hG.hasFDerivAt.mul ((hh k).hasFDerivAt.comp v hΦ.hasFDerivAt)).fderiv
  ext ξ k
  rw [jacM_apply, d0, dk]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, jacM_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul, PiLp.smul_apply]
  ring

theorem det_smul_V {n : ℕ} (c : ℂ) (M : V n →L[ℂ] V n) : (c • M).det = c ^ n * M.det := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_smul, LinearMap.det_smul,
    finrank_euclideanSpace_fin]

theorem jacM_det_diffAt {n : ℕ} {f0 : V n → ℂ} {f : Fin n → V n → ℂ} {U : Set (V n)}
    (hU : IsOpen U) (h0 : DifferentiableOn ℂ f0 U) (h : ∀ k, DifferentiableOn ℂ (f k) U)
    {v : V n} (hv : v ∈ U) : DifferentiableAt ℂ (fun w => (jacM f0 f w).det) v := by
  have c0 : ContDiffOn ℂ ∞ f0 U := ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ hU h0
  have ck : ∀ k, ContDiffOn ℂ ∞ (f k) U := fun k =>
    ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ hU (h k)
  have d0 : ContDiffOn ℂ ∞ (fderiv ℂ f0) U := c0.fderiv_of_isOpen hU (by simp)
  have dk : ∀ k, ContDiffOn ℂ ∞ (fderiv ℂ (f k)) U := fun k =>
    (ck k).fderiv_of_isOpen hU (by simp)
  have hn := hU.mem_nhds hv
  have hc : ContDiffAt ℂ ∞ (fun w => (jacM f0 f w).det) v := by
    simp_rw [flL_det_eq, jacM_apply]
    refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun c _ => ?_)
    exact ((c0.contDiffAt hn).mul (((dk _).contDiffAt hn).clm_apply contDiffAt_const)).sub
      (((ck _).contDiffAt hn).mul ((d0.contDiffAt hn).clm_apply contDiffAt_const))
  exact hc.differentiableAt (by simp)

theorem zLoc_fderiv {n : ℕ} (f0 : V n → ℂ) (f : Fin n → V n → ℂ) (v : V n)
    (h0 : DifferentiableAt ℂ f0 v) (h : ∀ k, DifferentiableAt ℂ (f k) v) (hne : f0 v ≠ 0) :
    fderiv ℂ (fun w => (WithLp.toLp 2 (fun k => f k w / f0 w) : V n)) v =
      ((f0 v ^ 2)⁻¹) • jacM f0 f v := by
  have hinv : HasFDerivAt (fun w => (f0 w)⁻¹) (-((f0 v) ^ 2)⁻¹ • fderiv ℂ f0 v) v :=
    (hasDerivAt_inv hne).comp_hasFDerivAt v h0.hasFDerivAt
  have hk : ∀ k, HasFDerivAt (fun w => f k w / f0 w)
      (f k v • (-((f0 v) ^ 2)⁻¹ • fderiv ℂ f0 v) + (f0 v)⁻¹ • fderiv ℂ (f k) v) v := by
    intro k
    exact ((h k).hasFDerivAt.mul hinv).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w => by simp [div_eq_mul_inv])
  have hpi := hasFDerivAt_pi.2 hk
  have hE := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm :
    (Fin n → ℂ) →L[ℂ] V n).hasFDerivAt.comp v hpi
  rw [show (fun w => (WithLp.toLp 2 (fun k => f k w / f0 w) : V n)) =
    (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm : (Fin n → ℂ) →L[ℂ] V n) ∘
      fun w k => f k w / f0 w) from rfl, hE.fderiv]
  ext ξ k
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, PiLp.smul_apply,
    jacM_apply, smul_eq_mul]
  simp
  field_simp
  ring

theorem jac_section : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (B : La) (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ), A.IsSec B t0 → (∀ j, A.IsSec B (t j)) → ∃ J : ι → Y → ℂ, A.IsSec (A.kap + (2 * n) • B) J ∧ ∀ i y, y ∈ (A.chart i).source → t0 i y ≠ 0 → J i y = t0 i y ^ (2 * n) * (fderiv ℂ (A.zLoc t0 t i) (A.chart i y)).det := by
  intro n Y _ _ _ _ _ ι La _ A B t0 t h0 ht
  have hd0 : ∀ i, DifferentiableOn ℂ (t0 i ∘ (A.chart i).symm) (A.chart i).target := fun i => by
    simpa using h0.1 i
  have hdk : ∀ i k, DifferentiableOn ℂ (t k i ∘ (A.chart i).symm) (A.chart i).target :=
    fun i k => by simpa using (ht k).1 i
  refine ⟨fun i y => (jacM (t0 i ∘ (A.chart i).symm) (fun k => t k i ∘ (A.chart i).symm)
    (A.chart i y)).det, ⟨fun i => ?_, ?_⟩, ?_⟩
  · intro v hv
    have hvt : v ∈ (A.chart i).target := hv.1
    exact (jacM_det_diffAt (A.chart i).open_target (hd0 i) (hdk i) hvt).differentiableWithinAt.congr
      (fun w hw => by simp [(A.chart i).right_inv hw.1]) (by simp [(A.chart i).right_inv hvt])
  · intro i j y _ hi hj
    have hov : IsOpen (ovl A.chart i j) :=
      (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
    have hmov : A.chart i y ∈ ovl A.chart i j :=
      ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hj]⟩
    have hΦv : (A.chart j ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
      simp [(A.chart i).left_inv hi]
    have hEv : ∀ s : ι → Y → ℂ, A.IsSec B s → s i ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i y)]
        fun w => (A.g B i j ∘ (A.chart i).symm) w *
          (s j ∘ (A.chart j).symm) ((A.chart j ∘ (A.chart i).symm) w) := by
      intro s hs
      filter_upwards [hov.mem_nhds hmov] with w hw
      have hsi : (A.chart i).symm w ∈ (A.chart i).source := (A.chart i).map_target hw.1
      simp only [Function.comp_apply]
      rw [(A.chart j).left_inv hw.2]
      exact hs.2 i j _ trivial hsi hw.2
    have hG : DifferentiableAt ℂ (A.g B i j ∘ (A.chart i).symm) (A.chart i y) :=
      (A.holo_g B i j).differentiableAt (hov.mem_nhds hmov)
    have hΦ : DifferentiableAt ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y) :=
      (A.holo_trans i j).differentiableAt (hov.mem_nhds hmov)
    have hjt : (A.chart j).target ∈ 𝓝 ((A.chart j ∘ (A.chart i).symm) (A.chart i y)) := by
      rw [hΦv]; exact (A.chart j).open_target.mem_nhds ((A.chart j).map_source hj)
    have key := jacM_trans (A.g B i j ∘ (A.chart i).symm) (A.chart j ∘ (A.chart i).symm)
      (t0 j ∘ (A.chart j).symm) (fun k => t k j ∘ (A.chart j).symm) (A.chart i y) hG hΦ
      ((hd0 j).differentiableAt hjt) (fun k => (hdk j k).differentiableAt hjt)
    rw [hΦv] at key
    have hcong := jacM_congr (hEv t0 h0) (fun k => hEv (t k) (ht k))
    have hdc : ((jacM (t0 j ∘ (A.chart j).symm) (fun k => t k j ∘ (A.chart j).symm)
        (A.chart j y)).comp (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y))).det =
        (jacM (t0 j ∘ (A.chart j).symm) (fun k => t k j ∘ (A.chart j).symm) (A.chart j y)).det *
        (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y)).det := LinearMap.det_comp _ _
    simp only
    rw [hcong, key, det_smul_V, hdc, A.g_add _ _ i j y hi hj, bsA_g_nsmul A B _ hi hj,
      A.g_kap i j y hi hj]
    simp only [Function.comp_apply, (A.chart i).left_inv hi]
    rw [← pow_mul]
    ring
  · intro i y hi hne
    have hyt : A.chart i y ∈ (A.chart i).target := (A.chart i).map_source hi
    have hn := (A.chart i).open_target.mem_nhds hyt
    have hne' : (t0 i ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
      simpa [(A.chart i).left_inv hi] using hne
    have hz := zLoc_fderiv (t0 i ∘ (A.chart i).symm) (fun k => t k i ∘ (A.chart i).symm)
      (A.chart i y) ((hd0 i).differentiableAt hn) (fun k => (hdk i k).differentiableAt hn) hne'
    have hzl : A.zLoc t0 t i = fun w => (WithLp.toLp 2 (fun k =>
        (t k i ∘ (A.chart i).symm) w / (t0 i ∘ (A.chart i).symm) w) : V n) := rfl
    simp only
    rw [hzl, hz, det_smul_V]
    simp only [Function.comp_apply, (A.chart i).left_inv hi] at hne' ⊢
    rw [← mul_assoc, ← inv_pow, pow_mul, ← mul_pow]
    rw [show t0 i y ^ 2 * (t0 i y)⁻¹ ^ 2 = 1 by field_simp, one_pow, one_mul]

end

end GlobalTheory.JacSec
