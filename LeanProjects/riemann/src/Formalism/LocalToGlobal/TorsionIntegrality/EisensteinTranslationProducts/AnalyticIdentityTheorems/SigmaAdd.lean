import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine

noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F
namespace SigmaAdditionFormula

variable (L : PeriodPair) (w : ℂ)

def additionQuotient (z : ℂ) : ℂ :=
  wSigma L (z + w) * wSigma L (z - w) / wSigma L z ^ 2 + wSigma L w ^ 2 * L.weierstrassP z

def frobeniusStickelbergerDetMulSigmaCube (z : ℂ) : ℂ :=
  wSigma L (z + w) * wSigma L (z - w)
    + wSigma L w ^ 2 * (dslope (wSigma L) 0 z ^ 2 + wSigma L z ^ 2 * L.weierstrassPExcept 0 z)

lemma semiChar_sq (ω : ℂ) : semiChar L ω ^ 2 = 1 := by
  unfold semiChar
  split_ifs <;> norm_num

lemma additionQuotient_periodic (hq : SigmaQuasi) : IsPeriodic L (additionQuotient L w) := by
  intro ω hω z
  have h1 := hq L ω (z + w) hω
  have h2 := hq L ω (z - w) hω
  have h0 := hq L ω z hω
  have hP : L.weierstrassP (z + ω) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨ω, hω⟩
  have hs := semiChar_sq L ω
  have he : Complex.exp (wEta L ω * (z + w + ω / 2)) * Complex.exp (wEta L ω * (z - w + ω / 2))
      = Complex.exp (wEta L ω * (z + ω / 2)) ^ 2 := by
    rw [← Complex.exp_add, sq, ← Complex.exp_add]
    congr 1
    ring
  have hne : Complex.exp (wEta L ω * (z + ω / 2)) ^ 2 ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
  unfold additionQuotient
  rw [show z + ω + w = (z + w) + ω by ring, show z + ω - w = (z - w) + ω by ring, h1, h2, h0, hP]
  congr 1
  calc _ = (semiChar L ω ^ 2 * (Complex.exp (wEta L ω * (z + w + ω / 2))
          * Complex.exp (wEta L ω * (z - w + ω / 2)))) * (wSigma L (z + w) * wSigma L (z - w))
          / ((semiChar L ω ^ 2 * Complex.exp (wEta L ω * (z + ω / 2)) ^ 2) * wSigma L z ^ 2) := by
        ring
    _ = _ := by rw [hs, he, one_mul, mul_div_mul_left _ _ hne]

lemma analyticAt_dslope (he : SigmaEntire) : AnalyticAt ℂ (dslope (wSigma L) 0) 0 := by
  obtain ⟨p, hp⟩ := (he L).analyticAt 0
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

lemma sigma_zero (hz : SigmaZero) : wSigma L 0 = 0 := (hz L 0).2 L.lattice.zero_mem

lemma dslope_neg (ho : SigmaOdd) (z : ℂ) : dslope (wSigma L) 0 (-z) = dslope (wSigma L) 0 z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · rw [neg_zero]
  · have h0 : wSigma L 0 = 0 := by
      have := ho L 0
      rw [neg_zero] at this
      linear_combination this / 2
    rw [dslope_of_ne _ (neg_ne_zero.2 hz0), dslope_of_ne _ hz0, slope_def_field, slope_def_field,
      ho L z, h0, sub_zero, sub_zero, sub_zero, sub_zero, neg_div_neg_eq]

lemma additionNumerator_neg (ho : SigmaOdd) (z : ℂ) : frobeniusStickelbergerDetMulSigmaCube L w (-z) = frobeniusStickelbergerDetMulSigmaCube L w z := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  rw [dslope_neg L ho z, ho L z, L.weierstrassPExcept_neg, neg_zero,
    show -z + w = -(z - w) by ring, show -z - w = -(z + w) by ring, ho L (z - w), ho L (z + w)]
  ring

lemma twistedGamma_analyticAt_zero (he : SigmaEntire) : AnalyticAt ℂ (frobeniusStickelbergerDetMulSigmaCube L w) 0 := by
  have hσd : Differentiable ℂ (wSigma L) := he L
  have hs : ∀ c : ℂ, AnalyticAt ℂ (fun z => wSigma L (z + c)) 0 := fun c =>
    (hσd.comp (differentiable_id.add_const c)).analyticAt 0
  have hs' : ∀ c : ℂ, AnalyticAt ℂ (fun z => wSigma L (z - c)) 0 := fun c =>
    (hσd.comp (differentiable_id.sub_const c)).analyticAt 0
  have hP : AnalyticAt ℂ (L.weierstrassPExcept 0) 0 :=
    L.analyticOnNhd_weierstrassPExcept 0 0 (by simp)
  have hd := analyticAt_dslope L he
  have hσ : AnalyticAt ℂ (wSigma L) 0 := hσd.analyticAt 0
  exact ((hs w).mul (hs' w)).add (analyticAt_const.mul ((hd.pow 2).add ((hσ.pow 2).mul hP)))

lemma twistedGamma_zero (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple) : frobeniusStickelbergerDetMulSigmaCube L w 0 = 0 := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  rw [dslope_same, (hs L).1, sigma_zero L hz, zero_add, zero_sub, ho L w]
  ring

private lemma weierstrassP_eq_except_zero_add_inv_sq (z : ℂ) : L.weierstrassP z = L.weierstrassPExcept 0 z + 1 / z ^ 2 := by
  rw [← L.weierstrassPExcept_add 0 z]
  simp

private lemma eventually_not_mem_lattice_punctured_zero : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
  have hD : DiscreteTopology (L.lattice : Set ℂ) := (inferInstance : DiscreteTopology L.lattice)
  exact Filter.inf_principal_eq_bot.1 (discreteTopology_subtype_iff.1 hD 0 L.lattice.zero_mem)

lemma additionQuotient_mul_eventuallyEq (hz : SigmaZero) :
    (fun z => additionQuotient L w z * wSigma L z ^ 2) =ᶠ[𝓝[≠] 0] frobeniusStickelbergerDetMulSigmaCube L w := by
  filter_upwards [eventually_not_mem_lattice_punctured_zero L, self_mem_nhdsWithin] with z hzL hz0
  have hσ : wSigma L z ≠ 0 := fun h => hzL ((hz L z).1 h)
  have hz0' : z ≠ 0 := hz0
  have h0 := sigma_zero L hz
  have hd : dslope (wSigma L) 0 z = wSigma L z / z := by
    rw [dslope_of_ne _ hz0', slope_def_field, h0, sub_zero, sub_zero]
  unfold additionQuotient frobeniusStickelbergerDetMulSigmaCube
  rw [weierstrassP_eq_except_zero_add_inv_sq L z, hd]
  field_simp
  ring

private lemma exists_twistedGamma_eq_sq_mul_analytic (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple) :
    ∃ m : ℂ → ℂ, AnalyticAt ℂ m 0 ∧ ∀ y, frobeniusStickelbergerDetMulSigmaCube L w y = y ^ 2 * m y := by
  have hg0 := twistedGamma_zero L w ho hz hs

  have hder : deriv (frobeniusStickelbergerDetMulSigmaCube L w) 0 = 0 := by
    have h1 : deriv (fun y => frobeniusStickelbergerDetMulSigmaCube L w (-y)) 0 = -deriv (frobeniusStickelbergerDetMulSigmaCube L w) (-0) :=
      deriv_comp_neg (f := frobeniusStickelbergerDetMulSigmaCube L w) (x := 0)
    have h2 : (fun y => frobeniusStickelbergerDetMulSigmaCube L w (-y)) = frobeniusStickelbergerDetMulSigmaCube L w := funext (additionNumerator_neg L w ho)
    rw [h2, neg_zero] at h1
    linear_combination h1 / 2
  obtain ⟨p, hp⟩ := twistedGamma_analyticAt_zero L w he
  have hm := hp.has_fpower_series_dslope_fslope.has_fpower_series_dslope_fslope
  refine ⟨dslope (dslope (frobeniusStickelbergerDetMulSigmaCube L w) 0) 0, ⟨_, hm⟩, fun y => ?_⟩
  have e1 := sub_smul_dslope (frobeniusStickelbergerDetMulSigmaCube L w) 0 y
  have e2 := sub_smul_dslope (dslope (frobeniusStickelbergerDetMulSigmaCube L w) 0) 0 y
  rw [dslope_same, hder] at e2
  simp only [sub_zero, smul_eq_mul, hg0] at e1 e2
  rw [← e1, ← e2]
  ring

lemma additionNumerator_order (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple) :
    (2 : WithTop ℤ) ≤ meromorphicOrderAt (frobeniusStickelbergerDetMulSigmaCube L w) 0 := by
  obtain ⟨m, hm, hgm⟩ := exists_twistedGamma_eq_sq_mul_analytic L w he ho hz hs
  have hfun : frobeniusStickelbergerDetMulSigmaCube L w = (fun y : ℂ => y ^ 2) * m := funext fun y => hgm y
  have hmer : MeromorphicAt (fun y : ℂ => y ^ 2) 0 := (analyticAt_id.pow 2).meromorphicAt
  have h2 : meromorphicOrderAt (fun y : ℂ => y ^ 2) 0 = ((2 : ℤ) : WithTop ℤ) :=
    (meromorphicOrderAt_eq_int_iff hmer).2
      ⟨fun _ => 1, analyticAt_const, one_ne_zero, Filter.Eventually.of_forall fun y => by simp⟩
  rw [hfun, meromorphicOrderAt_mul hmer hm.meromorphicAt, h2]
  have h3 := hm.meromorphicOrderAt_nonneg
  calc (2 : WithTop ℤ) = ((2 : ℤ) : WithTop ℤ) + 0 := by norm_cast
    _ ≤ ((2 : ℤ) : WithTop ℤ) + meromorphicOrderAt m 0 := add_le_add le_rfl h3

private lemma meromorphicAt_weierstrassP (z : ℂ) : MeromorphicAt L.weierstrassP z := by
  classical
  obtain ⟨l, hl⟩ : ∃ l : L.lattice, z ∉ (L.lattice : Set ℂ) \ {(l : ℂ)} := by
    by_cases h : z ∈ L.lattice
    · exact ⟨⟨z, h⟩, fun h' => h'.2 rfl⟩
    · exact ⟨0, fun h' => h h'.1⟩
  have e : L.weierstrassP = fun x => L.weierstrassPExcept l x + (1 / (x - l) ^ 2 - 1 / (l : ℂ) ^ 2) :=
    funext fun x => (L.weierstrassPExcept_add l x).symm
  rw [e]
  exact (L.analyticOnNhd_weierstrassPExcept l z hl).meromorphicAt.add
    ((analyticAt_const.meromorphicAt.div ((analyticAt_id.sub analyticAt_const).pow 2).meromorphicAt).sub
      analyticAt_const.meromorphicAt)

lemma additionQuotient_meromorphicAt (he : SigmaEntire) (z : ℂ) : MeromorphicAt (additionQuotient L w) z := by
  have hσd : Differentiable ℂ (wSigma L) := he L
  have a1 : AnalyticAt ℂ (fun x => wSigma L (x + w)) z :=
    (hσd.comp (differentiable_id.add_const w)).analyticAt z
  have a2 : AnalyticAt ℂ (fun x => wSigma L (x - w)) z :=
    (hσd.comp (differentiable_id.sub_const w)).analyticAt z
  have a3 : AnalyticAt ℂ (wSigma L) z := hσd.analyticAt z
  exact ((a1.mul a2).meromorphicAt.div (a3.pow 2).meromorphicAt).add
    (analyticAt_const.meromorphicAt.mul (meromorphicAt_weierstrassP L z))

lemma additionQuotient_analyticAt (he : SigmaEntire) (hz : SigmaZero) (z : ℂ) (hzL : z ∉ L.lattice) :
    AnalyticAt ℂ (additionQuotient L w) z := by
  have hσd : Differentiable ℂ (wSigma L) := he L
  have a1 : AnalyticAt ℂ (fun x => wSigma L (x + w)) z :=
    (hσd.comp (differentiable_id.add_const w)).analyticAt z
  have a2 : AnalyticAt ℂ (fun x => wSigma L (x - w)) z :=
    (hσd.comp (differentiable_id.sub_const w)).analyticAt z
  have a3 : AnalyticAt ℂ (wSigma L) z := hσd.analyticAt z
  have hσz : wSigma L z ≠ 0 := fun h => hzL ((hz L z).1 h)
  have hz0 : z ∉ (L.lattice : Set ℂ) \ {0} := fun h => hzL h.1
  have hzne : z ≠ 0 := by
    rintro rfl
    exact hzL L.lattice.zero_mem
  have hP : AnalyticAt ℂ L.weierstrassP z := by
    rw [show L.weierstrassP = fun x => L.weierstrassPExcept 0 x + 1 / x ^ 2 from funext (weierstrassP_eq_except_zero_add_inv_sq L)]
    exact (L.analyticOnNhd_weierstrassPExcept 0 z hz0).add
      (analyticAt_const.div (analyticAt_id.pow 2) (pow_ne_zero _ hzne))
  exact ((a1.mul a2).div (a3.pow 2) (pow_ne_zero _ hσz)).add (analyticAt_const.mul hP)

private lemma exists_analytic_eq_additionQuotient_near_zero (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple) :
    ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ additionQuotient L w =ᶠ[𝓝[≠] 0] A := by
  obtain ⟨m, hm, hgm⟩ := exists_twistedGamma_eq_sq_mul_analytic L w he ho hz hs
  have hd : AnalyticAt ℂ (dslope (wSigma L) 0) 0 := analyticAt_dslope L he
  have hd0 : dslope (wSigma L) 0 0 ≠ 0 := by
    rw [dslope_same, (hs L).1]
    exact one_ne_zero
  have hσ : ∀ y, wSigma L y = y * dslope (wSigma L) 0 y := fun y => by
    have := sub_smul_dslope (wSigma L) 0 y
    simp only [sub_zero, smul_eq_mul, sigma_zero L hz] at this
    exact this.symm
  refine ⟨fun y => m y / dslope (wSigma L) 0 y ^ 2, hm.div (hd.pow 2) (pow_ne_zero _ hd0), ?_⟩
  have hdne : ∀ᶠ y in 𝓝[≠] (0 : ℂ), dslope (wSigma L) 0 y ≠ 0 :=
    (hd.continuousAt.eventually_ne hd0).filter_mono nhdsWithin_le_nhds
  filter_upwards [additionQuotient_mul_eventuallyEq L w hz, hdne, self_mem_nhdsWithin] with y h1 h2 h3
  have hy : y ≠ 0 := h3
  rw [hgm, hσ y] at h1
  rw [eq_div_iff (pow_ne_zero _ h2)]
  apply mul_left_cancel₀ (pow_ne_zero 2 hy)
  linear_combination h1

lemma additionQuotient_order_zero (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple)
    (hord : SigmaOrder) : 0 ≤ meromorphicOrderAt (additionQuotient L w) 0 := by
  obtain ⟨A, hA, hfA⟩ := exists_analytic_eq_additionQuotient_near_zero L w he ho hz hs
  rw [meromorphicOrderAt_congr hfA]
  exact hA.meromorphicOrderAt_nonneg

lemma additionQuotient_order (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero) (hs : SigmaSimple)
    (hq : SigmaQuasi) (hord : SigmaOrder) (z : ℂ) : 0 ≤ meromorphicOrderAt (additionQuotient L w) z := by
  by_cases hzL : z ∈ L.lattice
  · obtain ⟨A, hA, hfA⟩ := exists_analytic_eq_additionQuotient_near_zero L w he ho hz hs
    have hfun : additionQuotient L w = fun x => additionQuotient L w (x - z) := funext fun x => by
      have := additionQuotient_periodic L w hq (-z) (neg_mem hzL) x
      rw [← sub_eq_add_neg] at this
      exact this.symm
    have ht : Filter.Tendsto (fun x => x - z) (𝓝[≠] z) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (((continuous_id.sub continuous_const).tendsto' z 0 (sub_self z)).mono_left
          nhdsWithin_le_nhds)
        (Filter.mem_of_superset self_mem_nhdsWithin fun x hx => sub_ne_zero.2 hx)
    have h2 : (fun x => additionQuotient L w (x - z)) =ᶠ[𝓝[≠] z] fun x => A (x - z) := ht.eventually hfA
    rw [hfun, meromorphicOrderAt_congr h2]
    exact (hA.comp_of_eq (analyticAt_id.sub analyticAt_const) (sub_self z)).meromorphicOrderAt_nonneg
  · exact (additionQuotient_analyticAt L w he hz z hzL).meromorphicOrderAt_nonneg

end SigmaAdditionFormula

open SigmaAdditionFormula in
theorem sigmaAdd_of (hN : EllipticNoPole) (he : SigmaEntire) (ho : SigmaOdd) (hz : SigmaZero)
    (hs : SigmaSimple) (hq : SigmaQuasi) (hord : SigmaOrder) : SigmaAdd := by
  intro L z w hzL hwL
  obtain ⟨c, hc⟩ := hN L (additionQuotient L w) (additionQuotient_meromorphicAt L w he) (additionQuotient_periodic L w hq)
    (additionQuotient_order L w he ho hz hs hq hord)
  have hfz := hc z (additionQuotient_analyticAt L w he hz z hzL).continuousAt
  have hfw := hc w (additionQuotient_analyticAt L w he hz w hwL).continuousAt
  have hσz : wSigma L z ≠ 0 := fun h => hzL ((hz L z).1 h)
  have h0 := sigma_zero L hz
  rw [← hfw] at hfz
  unfold additionQuotient at hfz
  rw [sub_self, h0, mul_zero, zero_div, zero_add] at hfz
  have e : wSigma L (z + w) * wSigma L (z - w) / wSigma L z ^ 2 * wSigma L z ^ 2
      = wSigma L (z + w) * wSigma L (z - w) := div_mul_cancel₀ _ (pow_ne_zero 2 hσz)
  linear_combination (wSigma L z ^ 2) * hfz - e

theorem sgStarAdd_of (h : SigmaAdd) : SgStarAdd := by
  intro L z w hz hw
  unfold sgStar
  have e := h L z w hz hw
  have ex : Complex.exp (-(s2 L) * (z + w) ^ 2 / 2) * Complex.exp (-(s2 L) * (z - w) ^ 2 / 2)
      = Complex.exp (-(s2 L) * z ^ 2 / 2) ^ 2 * Complex.exp (-(s2 L) * w ^ 2 / 2) ^ 2 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc _ = (wSigma L (z + w) * wSigma L (z - w)) * (Complex.exp (-(s2 L) * (z + w) ^ 2 / 2)
          * Complex.exp (-(s2 L) * (z - w) ^ 2 / 2)) := by ring
    _ = _ := by
        rw [e, ex]
        ring

theorem pInjective_of (h : SigmaAdd) (hz : SigmaZero) : PInjective := by
  intro L z w hzL hwL
  have e := h L z w hzL hwL
  have hσz : wSigma L z ≠ 0 := fun h' => hzL ((hz L z).1 h')
  have hσw : wSigma L w ≠ 0 := fun h' => hwL ((hz L w).1 h')
  constructor
  · intro hP
    rw [hP, sub_self, mul_zero, neg_zero] at e
    rcases mul_eq_zero.1 e with h1 | h1
    · exact Or.inr ((hz L _).1 h1)
    · exact Or.inl ((hz L _).1 h1)
  · intro hor
    have h0 : wSigma L (z + w) * wSigma L (z - w) = 0 := by
      rcases hor with h1 | h1
      · rw [(hz L _).2 h1, mul_zero]
      · rw [(hz L _).2 h1, zero_mul]
    rw [h0] at e
    have h3 : wSigma L z ^ 2 * wSigma L w ^ 2 * (L.weierstrassP z - L.weierstrassP w) = 0 := by
      linear_combination e
    rcases mul_eq_zero.1 h3 with h1 | h1
    · exact absurd h1 (mul_ne_zero (pow_ne_zero _ hσz) (pow_ne_zero _ hσw))
    · exact sub_eq_zero.1 h1

end Formalism.L2.Th1.F
