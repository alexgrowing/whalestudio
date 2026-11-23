import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHermExtend
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace HermExtend

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blkSq (z : (Σ k, ι k) → ℂ) (k : K) : ℝ :=
  ∑ i, ‖z ⟨k, i⟩‖ ^ 2

def proj (z : (Σ k, ι k) → ℂ) : (Σ k, ι k × ι k) → ℂ :=
  fun q => z ⟨q.1, q.2.1⟩ * starRingEnd ℂ (z ⟨q.1, q.2.2⟩) * ((blkSq z q.1 : ℝ) : ℂ)⁻¹

def secAt (z₀ : (Σ k, ι k) → ℂ) (Q : (Σ k, ι k × ι k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun p => ∑ j, Q ⟨p.1, (p.2, j)⟩ * z₀ ⟨p.1, j⟩

def coefAt (z₀ w : (Σ k, ι k) → ℂ) (k : K) : ℂ :=
  (∑ j, starRingEnd ℂ (w ⟨k, j⟩) * z₀ ⟨k, j⟩) * ((blkSq w k : ℝ) : ℂ)⁻¹

variable (ι) in

def blocksNe : Set ((Σ k, ι k) → ℂ) :=
  {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}

theorem blkSq_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (k : K) :
    blkSq (torusSmul c z) k = ‖c k‖ ^ 2 * blkSq z k := by
  unfold blkSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [torusSmul, norm_mul, mul_pow]

theorem blkSq_pos {z : (Σ k, ι k) → ℂ} (hz : z ∈ blocksNe ι) (k : K) : 0 < blkSq z k := by
  obtain ⟨i, hi⟩ := hz k
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg ‖z ⟨k, i⟩‖)
    (Finset.mem_univ i))

theorem blkSq_ofReal (z : (Σ k, ι k) → ℂ) (k : K) :
    ((blkSq z k : ℝ) : ℂ) = ∑ j, starRingEnd ℂ (z ⟨k, j⟩) * z ⟨k, j⟩ := by
  unfold blkSq
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_mul']

theorem proj_smul (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    proj (torusSmul c z) = proj z := by
  funext q
  have h3 : (((‖c q.1‖ ^ 2 * blkSq z q.1 : ℝ)) : ℂ) = c q.1 * starRingEnd ℂ (c q.1) * (blkSq z q.1 : ℂ) := by
    push_cast
    rw [Complex.mul_conj']
  have h2 : c q.1 * starRingEnd ℂ (c q.1) ≠ 0 :=
    mul_ne_zero (hc q.1) ((map_ne_zero _).2 (hc q.1))
  unfold proj
  rw [blkSq_smul, h3, mul_inv]
  simp only [torusSmul, map_mul]
  calc c q.1 * z ⟨q.1, q.2.1⟩ * (starRingEnd ℂ (c q.1) * starRingEnd ℂ (z ⟨q.1, q.2.2⟩)) *
        ((c q.1 * starRingEnd ℂ (c q.1))⁻¹ * ((blkSq z q.1 : ℝ) : ℂ)⁻¹)
      = (c q.1 * starRingEnd ℂ (c q.1)) * (c q.1 * starRingEnd ℂ (c q.1))⁻¹ *
        (z ⟨q.1, q.2.1⟩ * starRingEnd ℂ (z ⟨q.1, q.2.2⟩) * ((blkSq z q.1 : ℝ) : ℂ)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ h2, one_mul]

theorem secAt_proj (z₀ w : (Σ k, ι k) → ℂ) :
    secAt z₀ (proj w) = torusSmul (coefAt z₀ w) w := by
  funext p
  simp only [secAt, proj, torusSmul, coefAt, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem secAt_proj_self {z₀ : (Σ k, ι k) → ℂ} (hz : z₀ ∈ blocksNe ι) : secAt z₀ (proj z₀) = z₀ := by
  rw [secAt_proj]
  funext p
  have : coefAt z₀ z₀ p.1 = 1 := by
    unfold coefAt
    rw [← blkSq_ofReal]
    exact mul_inv_cancel₀ (by exact_mod_cast (blkSq_pos hz p.1).ne')
  simp [torusSmul, this]

theorem coef_ne_zero {c : K → ℂ} {w : (Σ k, ι k) → ℂ} (h : torusSmul c w ∈ blocksNe ι) (k : K) :
    c k ≠ 0 := by
  obtain ⟨i, hi⟩ := h k
  intro h0
  exact hi (by simp [torusSmul, h0])

theorem eq_smul_of_proj_eq {z w : (Σ k, ι k) → ℂ} (hz : z ∈ blocksNe ι) (h : proj w = proj z) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z = torusSmul c w := by
  have e : z = torusSmul (coefAt z w) w := by rw [← secAt_proj, h, secAt_proj_self hz]
  exact ⟨coefAt z w, coef_ne_zero (e ▸ hz), e⟩

local notation "𝕟" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem isOpen_blocksNe : IsOpen (blocksNe ι) := by
  have : blocksNe ι = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp [blocksNe]
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem contDiff_blkSq (k : K) : ContDiff ℝ 𝕟 (fun z : (Σ k, ι k) → ℂ => blkSq z k) := by
  unfold blkSq
  exact ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))

theorem contDiffOn_proj : ContDiffOn ℝ 𝕟 (proj (ι := ι)) (blocksNe ι) := by
  refine contDiffOn_pi.2 fun q => ?_
  unfold proj
  have hc : ContDiff ℝ 𝕟 (fun z : (Σ k, ι k) → ℂ => starRingEnd ℂ (z ⟨q.1, q.2.2⟩)) := by
    have := Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ (⟨q.1, q.2.2⟩ : Σ k, ι k)) (n := 𝕟)
    simpa [Function.comp_def, Complex.conjCLE_apply] using this
  refine ((contDiff_apply ℝ ℂ (⟨q.1, q.2.1⟩ : Σ k, ι k)).mul hc).contDiffOn.mul ?_
  refine ContDiffOn.inv ?_ fun z hz => ?_
  · exact (Complex.ofRealCLM.contDiff.comp (contDiff_blkSq q.1)).contDiffOn
  · exact_mod_cast (blkSq_pos hz q.1).ne'

theorem contDiff_secAt (z₀ : (Σ k, ι k) → ℂ) : ContDiff ℝ 𝕟 (secAt (ι := ι) z₀) := by
  refine contDiff_pi.2 fun p => ?_
  unfold secAt
  exact ContDiff.sum fun j _ => (contDiff_apply ℝ ℂ _).mul contDiff_const

theorem contDiffOn_refNorm (a : K → ℤ) : ContDiffOn ℝ 𝕟 (refNorm (ι := ι) a) (blocksNe ι) := by
  unfold refNorm
  refine contDiffOn_prod fun k _ => ?_
  exact ContDiffOn.rpow_const_of_ne (contDiff_blkSq k).contDiffOn fun z hz => (blkSq_pos hz k).ne'

def unitPts (P : Ideal (MRing ι)) : Set ((Σ k, ι k) → ℂ) :=
  {z | z ∈ mcPts P ∧ ∀ k, blkSq z k = 1}

theorem isCompact_unitPts (P : Ideal (MRing ι)) : IsCompact (unitPts P) := by
  have hset : unitPts P = {z | ∀ k, blkSq z k = 1} ∩
      ⋂ f ∈ P, {z | eval z (map (Int.castRingHom ℂ) f) = 0} := by
    ext z
    simp only [unitPts, mcPts, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨⟨_, h⟩, h1⟩; exact ⟨h1, h⟩
    · rintro ⟨h1, h⟩
      refine ⟨⟨fun k => ?_, h⟩, h1⟩
      by_contra hk
      push_neg at hk
      have h0 : blkSq z k = 0 := by simp [blkSq, hk]
      rw [h1 k] at h0
      exact one_ne_zero h0
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · rw [hset]
    refine IsClosed.inter ?_ ?_
    · simp only [Set.setOf_forall]
      exact isClosed_iInter fun k => isClosed_eq (contDiff_blkSq k).continuous continuous_const
    · exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  · refine (Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
    obtain ⟨k, i⟩ := p
    have h1 : ‖z ⟨k, i⟩‖ ^ 2 ≤ blkSq z k :=
      Finset.single_le_sum (f := fun i => ‖z ⟨k, i⟩‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
    rw [hz.2 k] at h1
    nlinarith [norm_nonneg (z ⟨k, i⟩)]

theorem proj_image_eq {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    proj '' mcPts P = proj '' unitPts P := by
  apply subset_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have hpos := blkSq_pos (ι := ι) hz.1
    let c : K → ℂ := fun k => (((Real.sqrt (blkSq z k))⁻¹ : ℝ) : ℂ)
    have hc : ∀ k, c k ≠ 0 := fun k =>
      Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 (hpos k)).ne')
    refine ⟨torusSmul c z, ⟨mcPts_smul hP c hc hz, fun k => ?_⟩, proj_smul c hc z⟩
    rw [blkSq_smul]
    have hn : ‖c k‖ = (Real.sqrt (blkSq z k))⁻¹ := by
      simp only [c, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 (hpos k)))
    rw [hn, inv_pow, Real.sq_sqrt (hpos k).le, inv_mul_cancel₀ (hpos k).ne']
  · exact Set.image_mono fun z hz => hz.1

theorem isClosed_projImage {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    IsClosed (proj '' mcPts P) := by
  rw [proj_image_eq hP]
  refine ((isCompact_unitPts P).image_of_continuousOn ?_).isClosed
  exact contDiffOn_proj.continuousOn.mono fun z hz => hz.1.1

def logRatio (a : K → ℤ) (F : ((Σ k, ι k) → ℂ) → ℝ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  Real.log (F z / refNorm a z)

variable {P : Ideal (MRing ι)} {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ}

theorem logRatio_smul
    (hF : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    logRatio a F (torusSmul c z) = logRatio a F z := by
  unfold logRatio
  rw [hF z hz c hc, refNorm_smul, mul_div_mul_left _ _
    (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k)))]

open Classical in

def descend (P : Ideal (MRing ι)) (a : K → ℤ) (F : ((Σ k, ι k) → ℂ) → ℝ) (Q : (Σ k, ι k × ι k) → ℂ) : ℝ :=
  if h : ∃ z ∈ mcPts P, proj z = Q then logRatio a F h.choose else 0

theorem descend_proj
    (hF : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    {w : (Σ k, ι k) → ℂ} (hw : w ∈ mcPts P) : descend P a F (proj w) = logRatio a F w := by
  have h : ∃ z ∈ mcPts P, proj z = proj w := ⟨w, hw, rfl⟩
  rw [descend, dif_pos h]
  obtain ⟨hz, hzw⟩ := h.choose_spec
  obtain ⟨c, hc, e⟩ := eq_smul_of_proj_eq hw.1 hzw
  calc logRatio a F h.choose = logRatio a F (torusSmul c h.choose) := (logRatio_smul hF hz hc).symm
    _ = logRatio a F w := by rw [← e]

theorem local_ext (hP : IsMultiHomogIdeal P) (hpos : ∀ z ∈ mcPts P, 0 < F z)
    (hF : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    (hS : SmoothAlong (mcPts P) F) {z₀ : (Σ k, ι k) → ℂ} (hz₀ : z₀ ∈ mcPts P) :
    ∃ W ∈ 𝓝 (proj z₀), ∃ g : ((Σ k, ι k × ι k) → ℂ) → ℝ, ContDiffOn ℝ 𝕟 g W ∧
      ∀ Q ∈ W ∩ proj '' mcPts P, g Q = descend P a F Q := by
  obtain ⟨U, hU, G, hG, hGF⟩ := hS z₀ hz₀
  let O := (interior U ∩ G ⁻¹' Set.Ioi 0) ∩ blocksNe ι
  have hOopen : IsOpen O :=
    ((hG.continuousOn.mono interior_subset).isOpen_inter_preimage isOpen_interior isOpen_Ioi).inter
      isOpen_blocksNe
  have hz₀O : z₀ ∈ O := by
    refine ⟨⟨mem_interior_iff_mem_nhds.2 hU, ?_⟩, hz₀.1⟩
    show 0 < G z₀
    rw [← hGF z₀ ⟨mem_of_mem_nhds hU, hz₀⟩]
    exact hpos z₀ hz₀
  refine ⟨secAt z₀ ⁻¹' O, ?_, fun Q => Real.log (G (secAt z₀ Q) / refNorm a (secAt z₀ Q)), ?_, ?_⟩
  · refine (contDiff_secAt z₀).continuous.continuousAt.preimage_mem_nhds ?_
    rw [secAt_proj_self hz₀.1]
    exact hOopen.mem_nhds hz₀O
  · have h1 : ContDiffOn ℝ 𝕟 (fun Q => G (secAt z₀ Q)) (secAt z₀ ⁻¹' O) :=
      (hG.mono interior_subset).comp (contDiff_secAt z₀).contDiffOn fun Q hQ => hQ.1.1
    have h2 : ContDiffOn ℝ 𝕟 (fun Q => refNorm a (secAt z₀ Q)) (secAt z₀ ⁻¹' O) :=
      (contDiffOn_refNorm a).comp (contDiff_secAt z₀).contDiffOn fun Q hQ => hQ.2
    refine (h1.div h2 fun Q hQ => (refNorm_pos a hQ.2).ne').log fun Q hQ => ?_
    exact (div_pos hQ.1.2 (refNorm_pos a hQ.2)).ne'
  · rintro Q ⟨hQ, w, hw, rfl⟩
    rw [descend_proj hF hw]
    have e := secAt_proj z₀ w
    have hc : ∀ k, coefAt z₀ w k ≠ 0 := coef_ne_zero (by rw [← e]; exact hQ.2)
    have hmem : torusSmul (coefAt z₀ w) w ∈ mcPts P := mcPts_smul hP _ hc hw
    have hU' : torusSmul (coefAt z₀ w) w ∈ U := by
      rw [← e]; exact interior_subset hQ.1.1
    show Real.log (G (secAt z₀ (proj w)) / refNorm a (secAt z₀ (proj w))) = _
    rw [e, ← hGF _ ⟨hU', hmem⟩]
    exact logRatio_smul hF hw hc

open scoped Manifold in

theorem exists_smooth_descend (hP : IsMultiHomogIdeal P) (hpos : ∀ z ∈ mcPts P, 0 < F z)
    (hF : ∀ z ∈ mcPts P, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → F (torusSmul c z) = (∏ k, ‖c k‖ ^ a k) * F z)
    (hS : SmoothAlong (mcPts P) F) :
    ∃ g : ((Σ k, ι k × ι k) → ℂ) → ℝ, ContDiff ℝ 𝕟 g ∧ ∀ z ∈ mcPts P, g (proj z) = logRatio a F z := by
  classical
  let C := proj '' mcPts P
  let t : ((Σ k, ι k × ι k) → ℂ) → Set ℝ := fun Q => if Q ∈ C then {descend P a F Q} else Set.univ
  have ht : ∀ Q, Convex ℝ (t Q) := fun Q => by
    by_cases h : Q ∈ C
    · simp only [t, if_pos h]; exact convex_singleton _
    · simp only [t, if_neg h]; exact convex_univ
  have Hloc : ∀ Q, ∃ U ∈ 𝓝 Q, ∃ g : ((Σ k, ι k × ι k) → ℂ) → ℝ,
      ContMDiffOn 𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) 𝓘(ℝ, ℝ) 𝕟 g U ∧ ∀ y ∈ U, g y ∈ t y := by
    intro Q
    by_cases hQ : Q ∈ C
    · obtain ⟨z₀, hz₀, rfl⟩ := hQ
      obtain ⟨W, hW, g, hg, hgC⟩ := local_ext hP hpos hF hS hz₀
      refine ⟨W, hW, g, contMDiffOn_iff_contDiffOn.2 hg, fun y hy => ?_⟩
      by_cases hy' : y ∈ C
      · simp only [t, if_pos hy']
        exact hgC y ⟨hy, hy'⟩
      · simp only [t, if_neg hy']
        trivial
    · refine ⟨Cᶜ, (isClosed_projImage hP).isOpen_compl.mem_nhds hQ, fun _ => 0, contMDiffOn_const,
        fun y hy => ?_⟩
      simp only [t, if_neg hy]
      trivial
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ, (Σ k, ι k × ι k) → ℂ)
    (n := (⊤ : ℕ∞)) ht Hloc
  refine ⟨g, contMDiff_iff_contDiff.1 g.contMDiff, fun z hz => ?_⟩
  have := hg (proj z)
  have hC : proj z ∈ C := Set.mem_image_of_mem proj hz
  have h2 : t (proj z) = {descend P a F (proj z)} := if_pos hC
  rw [h2, Set.mem_singleton_iff] at this
  rw [this, descend_proj hF hz]

end HermExtend

theorem HermExtend.proof : HermExtend.Statement := by
  intro K _ ι _ P a F hP hpos hF hS
  obtain ⟨g, hg, hgz⟩ := HermExtend.exists_smooth_descend hP hpos hF hS
  refine ⟨{ a := a, h := fun z => refNorm a z * Real.exp (g (HermExtend.proj z)),
            pos := fun z hz => mul_pos (refNorm_pos a hz) (Real.exp_pos _),
            smul := fun c z hc => ?_ }, rfl, ?_, fun z hz => ?_⟩
  · show refNorm a (torusSmul c z) * Real.exp (g (HermExtend.proj (torusSmul c z))) = _
    rw [refNorm_smul, HermExtend.proj_smul c hc]
    ring
  · exact (HermExtend.contDiffOn_refNorm a).mul (hg.comp_contDiffOn HermExtend.contDiffOn_proj).exp
  · show refNorm a z * Real.exp (g (HermExtend.proj z)) = F z
    rw [hgz z hz, HermExtend.logRatio,
      Real.exp_log (div_pos (hpos z hz) (refNorm_pos a hz.1))]
    field_simp [(refNorm_pos a hz.1).ne']

end GroundTheory.Heights₂.Heights.LowerBoundFree
