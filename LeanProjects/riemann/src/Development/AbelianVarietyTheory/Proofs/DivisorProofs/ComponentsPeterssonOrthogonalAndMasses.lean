import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NullMeasurableSetClassesOverFramesOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.CompPetOrth

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ}

section One

variable {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)

theorem framesOn_disjoint {Z Z' : Comp Xo c} (h : Z ≠ Z') : Disjoint (framesOn U Z) (framesOn U Z') := by
  rw [Set.disjoint_left]
  rintro z ⟨_, hz⟩ ⟨_, hz'⟩
  have s₀ : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c Z Z' h) (hz s₀) (hz' s₀)

def sqN (la : ∀ k, Wt (U.X k).Ψ r) (f : Rul Xo c) : AutQ V → ENNReal :=
  fun q => ‖ptN la (rdU U f) (dict q.out)‖ₑ ^ (2 : ℝ)

theorem ptN_rdU_of_not_dom (la : ∀ k, Wt (U.X k).Ψ r) (f : Rul Xo c) {z : Σ k, Frame (U.X k).Ψ r}
    (hz : z.2 ∉ (U.X z.1).dom) : ptN la (rdU U f) z = 0 := by
  have h0 : rdU U f z.1 z.2 = 0 := by simp [rdU, hz]
  simp only [ptN, Data.pnorm, h0, norm_zero, zero_mul]

theorem sqN_support (la : ∀ k, Wt (U.X k).Ψ r) {Z : Comp Xo c} {f : Rul Xo c} (hf : f ∈ suppOn Z) :
    Function.support (sqN U V dict la f) ⊆ classesOver V dict (framesOn U Z) := by
  intro q hq
  by_contra hn
  apply hq
  have h0 : ptN la (rdU U f) (dict q.out) = 0 := by
    simp only [ptN, Data.pnorm, rdU_eq_zero U hf hn, norm_zero, zero_mul]
  simp [sqN, h0]

theorem petAt_sq (x : ℝ) (μ : Measure (AutQ V)) (G : WTZ D.host.E) (f : Rul Xo c) :
    petAt U x V dict μ G f ^ 2 = lieFacZ Dw x G ^ 2 * (∫⁻ q, sqN U V dict (modelWt U G) f q ∂μ).toReal := by
  unfold petAt petE
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ENNReal.toReal_ofNat,
    ← ENNReal.toReal_rpow, mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num [sqN]

theorem petE_rdU_ne_top (μ : Measure (AutQ V)) [IsProbabilityMeasure μ] (la : ∀ k, Wt (U.X k).Ψ r)
    {f : Rul Xo c} (hP : rdU U f ∈ holSub U.X la) : petE V dict μ la (rdU U f) ≠ ⊤ := by
  have h : ∀ q : AutQ V, ‖ptN la (rdU U f) (dict q.out)‖ₑ ≤ supE U.X la (rdU U f) := fun q => by
    rw [Real.enorm_eq_ofReal (ptN_nonneg _ _ _)]
    by_cases hd : (dict q.out).2 ∈ (U.X (dict q.out).1).dom
    · exact le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (rdU U f p.1) p.2))
        ⟨(dict q.out).1, ⟨(dict q.out).2, hd⟩⟩
    · rw [ptN_rdU_of_not_dom U la f hd, ENNReal.ofReal_zero]
      exact bot_le
  refine ne_top_of_le_ne_top ?_ (eLpNorm_le_of_ae_enorm_bound (Filter.Eventually.of_forall h))
  rw [measure_univ, ENNReal.one_rpow, smul_eq_mul, mul_one]
  exact supE_ne_top U.X la hP

theorem lint_sqN_ne_top (μ : Measure (AutQ V)) [IsProbabilityMeasure μ] (la : ∀ k, Wt (U.X k).Ψ r)
    {f : Rul Xo c} (hP : rdU U f ∈ holSub U.X la) : ∫⁻ q, sqN U V dict la f q ∂μ ≠ ⊤ := by
  have h := petE_rdU_ne_top U V dict μ la hP
  rw [petE, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h
  intro ht
  apply h
  simp only [sqN] at ht
  norm_num at ht ⊢
  rw [ht]

theorem lint_sqN_sum [Fintype (Comp Xo c)] (μ : Measure (AutQ V))
    (hm : ∀ Z : Comp Xo c, NullMeasurableSet (classesOver V dict (framesOn U Z)) μ) (la : ∀ k, Wt (U.X k).Ψ r)
    (f : Comp Xo c → Rul Xo c) (hf : ∀ Z, f Z ∈ suppOn Z) :
    ∫⁻ q, sqN U V dict la (∑ Z, f Z) q ∂μ = ∑ Z, ∫⁻ q, sqN U V dict la (f Z) q ∂μ := by
  have hdisj : Pairwise (Function.onFun Disjoint fun Z => classesOver V dict (framesOn U Z)) :=
    fun Z Z' h => Set.disjoint_left.2 fun q h1 h2 => Set.disjoint_left.1 (framesOn_disjoint U h) h1 h2
  have hpt : ∀ Z, ∀ q ∈ classesOver V dict (framesOn U Z),
      sqN U V dict la (∑ Z, f Z) q = sqN U V dict la (f Z) q := by
    intro Z q hq
    have e : rdU U (∑ Z', f Z') (dict q.out).1 (dict q.out).2 = rdU U (f Z) (dict q.out).1 (dict q.out).2 := by
      rw [map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single Z]
      · intro Z' _ hZ'
        exact rdU_eq_zero U (hf Z') fun h => Set.disjoint_left.1 (framesOn_disjoint U hZ') h hq
      · intro h; exact absurd (Finset.mem_univ Z) h
    simp only [sqN, ptN, Data.pnorm, e]
  have hsupp : Function.support (sqN U V dict la (∑ Z, f Z)) ⊆ ⋃ Z, classesOver V dict (framesOn U Z) := by
    intro q hq
    by_contra hn
    simp only [Set.mem_iUnion, not_exists] at hn
    apply hq
    have e : rdU U (∑ Z', f Z') (dict q.out).1 (dict q.out).2 = 0 := by
      rw [map_sum, Finset.sum_apply, Finset.sum_apply]
      exact Finset.sum_eq_zero fun Z _ => rdU_eq_zero U (hf Z) (hn Z)
    have h0 : ptN la (rdU U (∑ Z', f Z')) (dict q.out) = 0 := by
      simp only [ptN, Data.pnorm, e, norm_zero, zero_mul]
    simp only [sqN, h0]
    simp
  rw [← setLIntegral_eq_of_support_subset hsupp, lintegral_iUnion₀ hm (fun Z Z' h => (hdisj h).aedisjoint),
    tsum_fintype]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [← setLIntegral_eq_of_support_subset (sqN_support U V dict la (hf Z))]
  exact lintegral_congr_ae ((ae_restrict_mem₀ (hm Z)).mono fun q hq => hpt Z q hq)

theorem petAt_muOn_sq (x : ℝ) (G : WTZ D.host.E) {Z : Comp Xo c} {f : Rul Xo c} (hf : f ∈ suppOn Z) :
    (muQ1 V (classesOver V dict (framesOn U Z))).toReal * petAt U x V dict (muOn U V dict Z) G f ^ 2 =
      petAt U x V dict (muQ1 V) G f ^ 2 := by
  rw [petAt_sq, petAt_sq]
  unfold muOn muPart ProbabilityTheory.cond
  have key := setLIntegral_eq_of_support_subset (μ := muQ1 V) (sqN_support U V dict (modelWt U G) hf)
  rw [lintegral_smul_measure, key]
  by_cases h0 : muQ1 V (classesOver V dict (framesOn U Z)) = 0
  · have hI : ∫⁻ q, sqN U V dict (modelWt U G) f q ∂muQ1 V = 0 := by
      rw [← key, Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]
    simp [h0, hI]
  · have ha : (muQ1 V (classesOver V dict (framesOn U Z))).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨h0, measure_ne_top _ _⟩
    rw [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
    field_simp

theorem petAt_idem_le (x : ℝ) (μ : Measure (AutQ V)) [IsProbabilityMeasure μ] (G : WTZ D.host.E) (Z : Comp Xo c)
    {f : Rul Xo c} (hP : rdU U f ∈ holSub U.X (modelWt U G)) :
    petAt U x V dict μ G (GlobalTheory.FlatLine.idem Z * f) ≤ petAt U x V dict μ G f := by
  unfold petAt
  refine mul_le_mul_of_nonneg_left ?_ (lieFacZ_pos _ _).le
  refine ENNReal.toReal_mono (petE_rdU_ne_top U V dict μ _ hP) ?_
  unfold petE
  refine eLpNorm_mono fun q => ?_
  rw [Real.norm_of_nonneg (ptN_nonneg _ _ _), Real.norm_of_nonneg (ptN_nonneg _ _ _)]
  simp only [ptN, Data.pnorm]
  refine mul_le_mul_of_nonneg_right ?_ (pnorm_fac_nonneg _ _ _)
  rw [GlobalTheory.AllWt.rdU_mul, Pi.mul_apply, Pi.mul_apply, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  have he : IsIdempotentElem (rdU U (GlobalTheory.FlatLine.idem Z) (dict q.out).1 (dict q.out).2) := by
    have := congrFun (congrFun (GlobalTheory.AllWt.rdU_mul U (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z)) (dict q.out).1)
      (dict q.out).2
    rw [GlobalTheory.FlatLine.idem_mul_idem] at this
    exact this.symm
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 he with h | h <;> rw [h] <;> simp

end One

theorem orthogonal_mass_idem : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ G : WTZ D.host.E, Orthogonal U V dict G ∧ (∀ Z σ, 0 ≤ mass U V dict Z σ ∧ mass U V dict Z σ ≤ 1) ∧ ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ) (f : cuspW Xo c U G), petW U (xiR D) V dict G σ (idem Z * (f : Rul Xo c)) ≤ petW U (xiR D) V dict G σ (f : Rul Xo c) := by
  intro D H Dw l Xo c r U V dict hc G
  haveI := CompFin.finite_comp Xo c
  letI : Fintype (Comp Xo c) := Fintype.ofFinite _
  have hm : ∀ (σ : c.F →+* ℂ) (Z : Comp Xo c), NullMeasurableSet
      (classesOver (V (goodOf c σ)) (dict (goodOf c σ)) (framesOn (U (goodOf c σ)) Z)) (muQ1 (V (goodOf c σ))) :=
    fun σ Z => GlobalTheory.ClassesMeas.nullMeasurableSet_classesOver_framesOn D H Dw l Xo c r U V dict hc _
      (goodEmb_goodOf c σ) Z
  refine ⟨fun σ => ⟨fun f => ?_, fun Z f => ?_⟩, fun Z σ => ⟨ENNReal.toReal_nonneg, ?_⟩, fun Z σ f => ?_⟩
  · rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    simp only [normRes, petW]
    rw [petAt_sq, lint_sqN_sum _ _ _ _ (hm σ) _ _ fun Z => (Submodule.mem_inf.1 (f Z).2).2,
      ENNReal.toReal_sum fun Z _ => lint_sqN_ne_top _ _ _ _ _
        ((mem_cuspW.1 (Submodule.mem_inf.1 (f Z).2).1).2 _ (goodEmb_goodOf c σ)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun Z _ => (petAt_sq _ _ _ _ _ _ _).symm
  · simp only [normRes, normOn, petW, petOn, mass]
    exact (petAt_muOn_sq _ _ _ _ _ (Submodule.mem_inf.1 f.2).2).symm
  · simp only [mass]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  · simp only [petW]
    exact petAt_idem_le _ _ _ _ _ _ _ ((mem_cuspW.1 f.2).2 _ (goodEmb_goodOf c σ))

end GlobalTheory.CompPetOrth
