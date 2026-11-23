import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingWeight
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Set ComplexConjugate Manifold

noncomputable section

namespace EmbeddingWeight

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def blockNormSq (z : (Σ k, ι k) → ℂ) (k : K) : ℝ := ∑ i, ‖z ⟨k, i⟩‖ ^ 2

def projPt (z : (Σ k, ι k) → ℂ) : (Σ k, ι k × ι k) → ℂ :=
  fun q => z ⟨q.1, q.2.1⟩ * conj (z ⟨q.1, q.2.2⟩) / (blockNormSq z q.1 : ℂ)

def conjVec (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun p => conj (z p)

theorem blockNormSq_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) (k : K) :
    blockNormSq (fun p => c p.1 * z p) k = ‖c k‖ ^ 2 * blockNormSq z k := by
  simp [blockNormSq, norm_mul, mul_pow, Finset.mul_sum]

theorem blockNormSq_pos {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K) :
    0 < blockNormSq z k := by
  obtain ⟨i, hi⟩ := hz k
  exact Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩

theorem projPt_smul (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    projPt (fun p => c p.1 * z p) = projPt z := by
  funext q
  have hc2 : c q.1 * conj (c q.1) = ((‖c q.1‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hne : c q.1 * conj (c q.1) ≠ 0 := mul_ne_zero (hc q.1) ((map_ne_zero _).2 (hc q.1))
  simp only [projPt, blockNormSq_smul, map_mul, Complex.ofReal_mul]
  rw [← hc2, show c q.1 * z ⟨q.1, q.2.1⟩ * (conj (c q.1) * conj (z ⟨q.1, q.2.2⟩)) =
    (c q.1 * conj (c q.1)) * (z ⟨q.1, q.2.1⟩ * conj (z ⟨q.1, q.2.2⟩)) by ring, mul_div_mul_left _ _ hne]

theorem conjVec_smul (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    conjVec (fun p => c p.1 * z p) = fun p => conj (c p.1) * conjVec z p := by
  funext p
  simp [conjVec]

theorem conjVec_conjVec (z : (Σ k, ι k) → ℂ) : conjVec (conjVec z) = z := by
  funext p
  simp [conjVec]

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.setOf_forall, Set.setOf_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem conjVec_mem_blockNonzero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, conjVec z ⟨k, i⟩ ≠ 0 := fun k =>
  let ⟨i, hi⟩ := hz k
  ⟨i, (map_ne_zero _).2 hi⟩

theorem contDiff_conjVec : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (conjVec (ι := ι)) :=
  contDiff_pi.2 fun p => Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ p)

theorem contDiffOn_projPt :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (projPt (ι := ι)) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  refine contDiffOn_pi.2 fun q => ?_
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z : (Σ k, ι k) → ℂ => blockNormSq z q.1 :=
    ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ _)
  have hinv := hN.contDiffOn.inv (s := {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0})
    fun z hz => (blockNormSq_pos hz q.1).ne'
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z : (Σ k, ι k) → ℂ => conj (z ⟨q.1, q.2.2⟩) :=
    Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ _)
  have := (((contDiff_apply ℝ ℂ ⟨q.1, q.2.1⟩).mul hconj).contDiffOn).mul
    (Complex.ofRealCLM.contDiff.comp_contDiffOn hinv)
  refine this.congr fun z _ => ?_
  simp [projPt, div_eq_mul_inv]

theorem exists_smul_of_projPt_eq {z w : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) (h : projPt z = projPt w) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ w = fun p => c p.1 * z p := by
  have hNz : ∀ k, (blockNormSq z k : ℂ) ≠ 0 := fun k =>
    Complex.ofReal_ne_zero.2 (blockNormSq_pos hz k).ne'
  have hNw : ∀ k, (blockNormSq w k : ℂ) ≠ 0 := fun k =>
    Complex.ofReal_ne_zero.2 (blockNormSq_pos hw k).ne'
  choose j hj using hz
  have hrel : ∀ k i, z ⟨k, i⟩ * conj (z ⟨k, j k⟩) / (blockNormSq z k : ℂ) =
      w ⟨k, i⟩ * conj (w ⟨k, j k⟩) / (blockNormSq w k : ℂ) := fun k i => congrFun h ⟨k, (i, j k)⟩
  have hwj : ∀ k, w ⟨k, j k⟩ ≠ 0 := by
    intro k hk
    have e := hrel k (j k)
    rw [hk, map_zero, mul_zero, zero_div, div_eq_zero_iff] at e
    rcases e with e | e
    · exact hj k (mul_self_eq_zero.1 (by simpa [Complex.mul_conj] using e))
    · exact hNz k e
  refine ⟨fun k => conj (z ⟨k, j k⟩) * (blockNormSq w k : ℂ) /
    ((blockNormSq z k : ℂ) * conj (w ⟨k, j k⟩)), fun k => ?_, ?_⟩
  · exact div_ne_zero (mul_ne_zero ((map_ne_zero _).2 (hj k)) (hNw k))
      (mul_ne_zero (hNz k) ((map_ne_zero _).2 (hwj k)))
  · funext p
    obtain ⟨k, i⟩ := p
    have e := hrel k i
    have hcw : conj (w ⟨k, j k⟩) ≠ 0 := (map_ne_zero _).2 (hwj k)
    rw [div_eq_div_iff (hNz k) (hNw k)] at e
    show w ⟨k, i⟩ = _ * z ⟨k, i⟩
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero (hNz k) hcw)]
    linear_combination -e

theorem eval_conjVec (f : MRing ι) (z : (Σ k, ι k) → ℂ) :
    eval (conjVec z) (map (Int.castRingHom ℂ) f) = conj (eval z (map (Int.castRingHom ℂ) f)) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp, conjVec]

theorem conjVec_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) :
    conjVec z ∈ mcPts P :=
  ⟨conjVec_mem_blockNonzero hz.1, fun f hf => by rw [eval_conjVec, hz.2 f hf, map_zero]⟩

theorem liesOver_conjVec {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω]
    {y : (Σ k, ι k) → Ω} {sg : F →+* ℂ} {z : (Σ k, ι k) → ℂ} (hz : LiesOver y sg z) :
    LiesOver y (NumberField.ComplexEmbedding.conjugate sg) (conjVec z) := by
  intro d g h θ hg hh hgh
  rw [eval_conjVec, eval_conjVec, hz d g h θ hg hh hgh, map_mul,
    NumberField.ComplexEmbedding.conjugate_coe_eq]

theorem liesOver_smul {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω]
    {y : (Σ k, ι k) → Ω} {sg : F →+* ℂ} {z : (Σ k, ι k) → ℂ} (hz : LiesOver y sg z) (c : K → ℂ) :
    LiesOver y sg (fun p => c p.1 * z p) := by
  intro d g h θ hg hh hgh
  rw [eval_smul_homog g d hg, eval_smul_homog h d hh, hz d g h θ hg hh hgh]
  ring

theorem isClosed_liesOver {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (sg : F →+* ℂ) : IsClosed {z : (Σ k, ι k) → ℂ | LiesOver y sg z} := by
  simp only [LiesOver, Set.setOf_forall]
  exact isClosed_iInter fun d => isClosed_iInter fun g => isClosed_iInter fun h =>
    isClosed_iInter fun θ => isClosed_iInter fun _ => isClosed_iInter fun _ =>
      isClosed_iInter fun _ => isClosed_eq (MvPolynomial.continuous_eval _) (continuous_const.mul (MvPolynomial.continuous_eval _))

theorem isClosed_zeros (P : Ideal (MRing ι)) :
    IsClosed {z : (Σ k, ι k) → ℂ | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const

theorem isCompact_sphere : IsCompact {z : (Σ k, ι k) → ℂ | ∀ k, blockNormSq z k = 1} := by
  have hN : ∀ k, Continuous fun z : (Σ k, ι k) → ℂ => blockNormSq z k := fun k =>
    continuous_finset_sum _ fun i _ => ((continuous_apply _).norm).pow 2
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · simp only [Set.setOf_forall]
    exact isClosed_iInter fun k => isClosed_eq (hN k) continuous_const
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun z hz => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun p => ?_
    have h1 : ‖z ⟨p.1, p.2⟩‖ ^ 2 ≤ blockNormSq z p.1 :=
      Finset.single_le_sum (f := fun i => ‖z ⟨p.1, i⟩‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ p.2)
    rw [hz p.1] at h1
    nlinarith [norm_nonneg (z p)]

theorem exists_smul_sphere {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ ∀ k, blockNormSq (fun p => c p.1 * z p) k = 1 := by
  let c : K → ℂ := fun k => (((Real.sqrt (blockNormSq z k))⁻¹ : ℝ) : ℂ)
  refine ⟨c, fun k => ?_, fun k => ?_⟩
  · have := blockNormSq_pos hz k
    exact Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_pos.2 this).ne')
  · have := blockNormSq_pos hz k
    rw [blockNormSq_smul c z k]
    simp only [c]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (Real.sqrt_pos.2 this)), inv_pow, Real.sq_sqrt this.le,
      inv_mul_cancel₀ this.ne']

end EmbeddingWeight

open EmbeddingWeight in

theorem EmbeddingWeight.proof : EmbeddingWeight.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y Λ hpos hconjΛ huniq
  classical
  let S : (F →+* ℂ) → Set ((Σ k, ι k) → ℂ) := fun sg =>
    {z | z ∈ mcPts (mCoordIdeal y) ∧ LiesOver y sg z}
  let C : (F →+* ℂ) → Set ((Σ k, ι k × ι k) → ℂ) := fun sg => projPt '' S sg
  have hSmul : ∀ sg z (c : K → ℂ), (∀ k, c k ≠ 0) → z ∈ S sg → (fun p => c p.1 * z p) ∈ S sg :=
    fun sg z c hc hz => ⟨mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal y) c hc hz.1,
      liesOver_smul hz.2 c⟩
  have hC : ∀ sg, IsCompact (C sg) := by
    intro sg
    have hK : IsCompact (S sg ∩ {z | ∀ k, blockNormSq z k = 1}) := by
      refine isCompact_sphere.of_isClosed_subset ?_ inter_subset_right
      have : S sg ∩ {z | ∀ k, blockNormSq z k = 1} =
          ({z | ∀ f ∈ mCoordIdeal y, eval z (map (Int.castRingHom ℂ) f) = 0} ∩
            {z | LiesOver y sg z}) ∩ {z | ∀ k, blockNormSq z k = 1} := by
        ext z
        simp only [S, mcPts, mem_inter_iff, mem_setOf_eq]
        constructor
        · rintro ⟨⟨⟨-, h1⟩, h2⟩, h3⟩
          exact ⟨⟨h1, h2⟩, h3⟩
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨⟨⟨fun k => ?_, h1⟩, h2⟩, h3⟩
          by_contra hcon
          push_neg at hcon
          have := h3 k
          simp [blockNormSq, hcon] at this
      rw [this]
      exact ((isClosed_zeros _).inter (isClosed_liesOver y sg)).inter
        isCompact_sphere.isClosed
    have heq : C sg = projPt '' (S sg ∩ {z | ∀ k, blockNormSq z k = 1}) := by
      refine Subset.antisymm ?_ (image_mono inter_subset_left)
      rintro e ⟨z, hz, rfl⟩
      obtain ⟨c, hc, hc1⟩ := exists_smul_sphere hz.1.1
      exact ⟨_, ⟨hSmul sg z c hc hz, hc1⟩, projPt_smul c hc z⟩
    rw [heq]
    exact hK.image_of_continuousOn (contDiffOn_projPt.continuousOn.mono fun z hz => hz.1.1.1)
  have hdisj : ∀ sg tg, sg ≠ tg → Disjoint (C sg) (C tg) := by
    intro sg tg hne
    rw [Set.disjoint_left]
    rintro e ⟨z, ⟨hzP, hzs⟩, rfl⟩ ⟨w, ⟨hwP, hwt⟩, hw⟩
    obtain ⟨c, hc, rfl⟩ := exists_smul_of_projPt_eq hzP.1 hwP.1 hw.symm
    exact hne ((huniq _ hwP).unique (liesOver_smul hzs c) hwt)
  have hsep : ∀ sg, ∃ χ : ((Σ k, ι k × ι k) → ℂ) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ ∧
      (∀ᶠ e in 𝓝ˢ (⋃ tg ∈ Finset.univ.erase sg, C tg), χ e = 0) ∧
      (∀ᶠ e in 𝓝ˢ (C sg), χ e = 1) := by
    intro sg
    obtain ⟨f, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
      𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) (n := ⊤)
      (isClosed_biUnion_finset fun tg _ => (hC tg).isClosed) (hC sg).isClosed
      (Set.disjoint_iUnion₂_left.2 fun tg htg => hdisj tg sg (Finset.ne_of_mem_erase htg))
    exact ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, h0, h1⟩
  choose χ hχs hχ0 hχ1 using hsep
  let g : ((Σ k, ι k × ι k) → ℂ) → ℝ := fun e => ∑ sg, Real.log (Λ sg) * χ sg e
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g :=
    ContDiff.sum fun sg _ => contDiff_const.mul (hχs sg)

  have hloc : ∀ sg, ∀ e ∈ C sg, ∀ᶠ e' in 𝓝 e, g e' = Real.log (Λ sg) := by
    intro sg e he
    have : ∀ tg, ∀ᶠ e' in 𝓝 e, χ tg e' = if tg = sg then 1 else 0 := by
      intro tg
      by_cases htg : tg = sg
      · subst htg
        simpa using (hχ1 tg).filter_mono (nhds_le_nhdsSet he)
      · simp only [htg, if_false]
        exact (hχ0 tg).filter_mono (nhds_le_nhdsSet
          (Set.mem_iUnion₂.2 ⟨sg, Finset.mem_erase.2 ⟨Ne.symm htg, Finset.mem_univ _⟩, he⟩))
    filter_upwards [Filter.eventually_all.2 this] with e' he'
    simp only [g, he', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  let u : ((Σ k, ι k) → ℂ) → ℝ := fun z => (g (projPt z) + g (projPt (conjVec z))) / 2
  have hu_smul : ∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) →
      (fun z => -u z) (fun p => c p.1 * z p) = (fun z => -u z) z := by
    intro c z hc
    have h2 : projPt (conjVec (fun p => c p.1 * z p)) = projPt (conjVec z) := by
      rw [conjVec_smul]
      exact projPt_smul (fun k => conj (c k)) (fun k => (map_ne_zero _).2 (hc k)) _
    simp only [u, projPt_smul c hc, h2]
  refine ⟨HermLine.ofWeight (fun z => -u z) hu_smul, rfl, ?_, ?_, ?_⟩
  · have h1 := hg.comp_contDiffOn (contDiffOn_projPt (ι := ι))
    have h2 := hg.comp_contDiffOn ((contDiffOn_projPt (ι := ι)).comp contDiff_conjVec.contDiffOn
      fun z hz => conjVec_mem_blockNonzero hz)
    have hu := ((h1.add h2).div_const (2 : ℝ)).neg.neg
    exact Real.contDiff_exp.comp_contDiffOn hu
  · intro z
    change Real.exp (-(-u (conjVec z))) = Real.exp (-(-u z))
    simp only [u, conjVec_conjVec, add_comm]
  · intro z hz sg hsg
    have hzC : projPt z ∈ C sg := ⟨z, ⟨hz, hsg⟩, rfl⟩
    have hzC' : projPt (conjVec z) ∈ C (NumberField.ComplexEmbedding.conjugate sg) :=
      ⟨conjVec z, ⟨conjVec_mem_mcPts hz, liesOver_conjVec hsg⟩, rfl⟩
    have hcont : ContinuousAt projPt z :=
      contDiffOn_projPt.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds hz.1)
    have hcont' : ContinuousAt (fun w => projPt (conjVec w)) z :=
      (contDiffOn_projPt.continuousOn.continuousAt
        (isOpen_blockNonzero.mem_nhds (conjVec_mem_blockNonzero hz.1))).comp
        contDiff_conjVec.continuous.continuousAt
    filter_upwards [Filter.Tendsto.eventually hcont (hloc sg _ hzC),
      Filter.Tendsto.eventually hcont' (hloc _ _ hzC')] with w hw1 hw2
    change Real.exp (-(-u w)) = Λ sg
    simp only [u, hw1, hw2, hconjΛ, neg_neg, add_self_div_two, Real.exp_log (hpos sg)]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
