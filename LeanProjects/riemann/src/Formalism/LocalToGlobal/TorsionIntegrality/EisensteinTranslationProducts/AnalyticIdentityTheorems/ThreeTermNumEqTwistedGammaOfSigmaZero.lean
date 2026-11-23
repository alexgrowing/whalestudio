import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine

noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F

namespace ThreeTermRelation

lemma le_sub_of_add_le {o : WithTop ℤ} {m k : ℤ} (h : ((k + m : ℤ) : WithTop ℤ) ≤ o) :
    (k : WithTop ℤ) ≤ o - (m : WithTop ℤ) := by
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n =>
    have := WithTop.coe_le_coe.1 h
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
    exact WithTop.coe_le_coe.2 (by omega)

lemma semiChar_mul_self (L : PeriodPair) (ω : ℂ) : semiChar L ω * semiChar L ω = 1 := by
  unfold semiChar
  split_ifs <;> norm_num

lemma eq_of_eventuallyEq_punctured {f g : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z)
    (hg : ContinuousAt g z) (h : f =ᶠ[𝓝[≠] z] g) : f z = g z :=
  tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' h.symm)

lemma eventually_notMem (L : PeriodPair) (z : ℂ) : ∀ᶠ x in 𝓝[≠] z, x ∉ L.lattice := by
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_sdiff_singleton_mem_nhds z)] with x hx0 hx1
  have hx0' : x ≠ z := hx0
  simp_all

variable (L : PeriodPair) (b c : ℂ)

def threeTermDet (x : ℂ) : ℂ :=
  (L.weierstrassP b * L.derivWeierstrassP c - L.weierstrassP c * L.derivWeierstrassP b)
    - L.weierstrassP x * (L.derivWeierstrassP c - L.derivWeierstrassP b)
    + L.derivWeierstrassP x * (L.weierstrassP c - L.weierstrassP b)

def nAux (x : ℂ) : ℂ := threeTermDet L b c x * wSigma L x ^ 3

def threeTermDenom (x : ℂ) : ℂ := wSigma L (x + (b + c)) * wSigma L (x + -b) * wSigma L (x + -c)

def threeTermQuotient (x : ℂ) : ℂ := nAux L b c x / threeTermDenom L b c x

def frobeniusStickelbergerDetMulSigmaCube (x : ℂ) : ℂ :=
  (L.weierstrassP b * L.derivWeierstrassP c - L.weierstrassP c * L.derivWeierstrassP b)
      * wSigma L x ^ 3
    - (x * dslope (wSigma L) 0 x ^ 3 + L.weierstrassPExcept 0 x * wSigma L x ^ 3)
      * (L.derivWeierstrassP c - L.derivWeierstrassP b)
    + (-2 * dslope (wSigma L) 0 x ^ 3 + L.derivWeierstrassPExcept 0 x * wSigma L x ^ 3)
      * (L.weierstrassP c - L.weierstrassP b)

lemma sigma_zero (hz : SigmaZero) : wSigma L 0 = 0 := (hz L 0).2 (zero_mem _)

lemma analyticAt_dslope (he : SigmaEntire) : AnalyticAt ℂ (dslope (wSigma L) 0) 0 := by
  obtain ⟨p, hp⟩ := (he L).analyticAt 0
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

lemma wp_congr {x y : ℂ} (h : x + -y ∈ L.lattice) :
    L.weierstrassP x = L.weierstrassP y ∧ L.derivWeierstrassP x = L.derivWeierstrassP y := by
  have e : y + ((⟨x + -y, h⟩ : L.lattice) : ℂ) = x := by
    show y + (x + -y) = x
    ring
  have h1 := L.weierstrassP_add_coe y ⟨x + -y, h⟩
  have h2 := L.derivWeierstrassP_add_coe y ⟨x + -y, h⟩
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

lemma threeTermNum_eq_twistedGamma_of_sigmaZero (hz : SigmaZero) (x : ℂ) (hx : x ≠ 0) : nAux L b c x = frobeniusStickelbergerDetMulSigmaCube L b c x := by
  have hP := L.weierstrassPExcept_def 0 x
  have hP' := L.derivWeierstrassPExcept_def 0 x
  simp only [ZeroMemClass.coe_zero] at hP hP'
  unfold nAux threeTermDet frobeniusStickelbergerDetMulSigmaCube
  rw [hP, hP', dslope_of_ne _ hx, slope_def_field, sigma_zero L hz]
  field_simp
  ring

lemma twistedGamma_zero (hz : SigmaZero) (hs : SigmaSimple) :
    frobeniusStickelbergerDetMulSigmaCube L b c 0 = -2 * (L.weierstrassP c - L.weierstrassP b) := by
  unfold frobeniusStickelbergerDetMulSigmaCube
  rw [dslope_same, (hs L).1, sigma_zero L hz]
  ring

lemma twistedGamma_analyticAt_zero (he : SigmaEntire) : AnalyticAt ℂ (frobeniusStickelbergerDetMulSigmaCube L b c) 0 := by
  have h3 := analyticAt_dslope L he
  have h4 : AnalyticAt ℂ (wSigma L) 0 := (he L).analyticAt 0
  have h5 := L.analyticAt_weierstrassPExcept 0
  have h6 := L.analyticAt_derivWeierstrassPExcept 0
  unfold frobeniusStickelbergerDetMulSigmaCube
  fun_prop

lemma sig_analyticAt (he : SigmaEntire) (β z : ℂ) : AnalyticAt ℂ (fun w => wSigma L (w + β)) z :=
  ((he L).comp (differentiable_id.add_const β)).analyticAt z

lemma sig_order_mem (hord : SigmaOrder) {β z : ℂ} (h : z + β ∈ L.lattice) :
    meromorphicOrderAt (fun w => wSigma L (w + β)) z = ((1 : ℤ) : WithTop ℤ) := by
  have := hord L 1 β z one_ne_zero
  simp only [one_mul] at this
  rw [this, if_pos (by rwa [one_mul])]
  rfl

lemma sig_order_notMem (hord : SigmaOrder) {β z : ℂ} (h : z + β ∉ L.lattice) :
    meromorphicOrderAt (fun w => wSigma L (w + β)) z = ((0 : ℤ) : WithTop ℤ) := by
  have := hord L 1 β z one_ne_zero
  simp only [one_mul] at this
  rw [this, if_neg (by rwa [one_mul])]
  rfl

lemma sig_eventually_ne (he : SigmaEntire) (hord : SigmaOrder) (β z : ℂ) :
    ∀ᶠ x in 𝓝[≠] z, wSigma L (x + β) ≠ 0 := by
  refine (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (sig_analyticAt L he β z).meromorphicAt).1 ?_
  by_cases h : z + β ∈ L.lattice
  · rw [sig_order_mem L hord h]; exact WithTop.coe_ne_top
  · rw [sig_order_notMem L hord h]; exact WithTop.coe_ne_top

lemma threeTermDenom_eventually_ne (he : SigmaEntire) (hord : SigmaOrder) (z : ℂ) :
    ∀ᶠ x in 𝓝[≠] z, threeTermDenom L b c x ≠ 0 := by
  filter_upwards [sig_eventually_ne L he hord (b + c) z, sig_eventually_ne L he hord (-b) z,
    sig_eventually_ne L he hord (-c) z] with x h1 h2 h3
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

lemma threeTermDenom_analyticAt (he : SigmaEntire) (z : ℂ) : AnalyticAt ℂ (threeTermDenom L b c) z :=
  ((sig_analyticAt L he (b + c) z).mul (sig_analyticAt L he (-b) z)).mul
    (sig_analyticAt L he (-c) z)

lemma threeTermNum_analyticAt (he : SigmaEntire) (z : ℂ) (hzL : z ∉ L.lattice) :
    AnalyticAt ℂ (nAux L b c) z := by
  have h4 : AnalyticAt ℂ (wSigma L) z := (he L).analyticAt z
  have h5 := L.analyticOnNhd_weierstrassP z hzL
  have h6 := L.analyticOnNhd_derivWeierstrassP z hzL
  unfold nAux threeTermDet
  fun_prop

lemma threeTermNum_meromorphicAt (he : SigmaEntire) (z : ℂ) : MeromorphicAt (nAux L b c) z := by
  have h4 : MeromorphicAt (wSigma L) z := ((he L).analyticAt z).meromorphicAt
  have h5 := L.meromorphic_weierstrassP z
  have h6 := L.meromorphic_derivWeierstrassP z
  unfold nAux threeTermDet
  fun_prop

lemma threeTermQuotient_meromorphicAt (he : SigmaEntire) (z : ℂ) : MeromorphicAt (threeTermQuotient L b c) z :=
  (threeTermNum_meromorphicAt L b c he z).div (threeTermDenom_analyticAt L b c he z).meromorphicAt

lemma threeTermQuotient_periodic (hq : SigmaQuasi) : IsPeriodic L (threeTermQuotient L b c) := by
  intro ω hω x
  have h0 := hq L ω x hω
  have h1 : wSigma L (x + ω + (b + c))
      = semiChar L ω * Complex.exp (wEta L ω * (x + (b + c) + ω / 2)) * wSigma L (x + (b + c)) := by
    rw [← hq L ω (x + (b + c)) hω]; congr 1; ring
  have h2 : wSigma L (x + ω + -b)
      = semiChar L ω * Complex.exp (wEta L ω * (x + -b + ω / 2)) * wSigma L (x + -b) := by
    rw [← hq L ω (x + -b) hω]; congr 1; ring
  have h3 : wSigma L (x + ω + -c)
      = semiChar L ω * Complex.exp (wEta L ω * (x + -c + ω / 2)) * wSigma L (x + -c) := by
    rw [← hq L ω (x + -c) hω]; congr 1; ring
  have hP : L.weierstrassP (x + ω) = L.weierstrassP x := L.weierstrassP_add_coe x ⟨ω, hω⟩
  have hP' : L.derivWeierstrassP (x + ω) = L.derivWeierstrassP x :=
    L.derivWeierstrassP_add_coe x ⟨ω, hω⟩
  have hE : Complex.exp (wEta L ω * (x + (b + c) + ω / 2)) * Complex.exp (wEta L ω * (x + -b + ω / 2))
        * Complex.exp (wEta L ω * (x + -c + ω / 2))
      = Complex.exp (wEta L ω * (x + ω / 2)) ^ 3 := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hχ : semiChar L ω ≠ 0 := fun h => by simpa [h] using semiChar_mul_self L ω
  have hne : semiChar L ω ^ 3 * Complex.exp (wEta L ω * (x + ω / 2)) ^ 3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hχ) (pow_ne_zero _ (Complex.exp_ne_zero _))
  unfold threeTermQuotient nAux threeTermDenom threeTermDet
  rw [h0, h1, h2, h3, hP, hP']
  rw [← mul_div_mul_left _ (wSigma L (x + (b + c)) * wSigma L (x + -b) * wSigma L (x + -c)) hne]
  congr 1
  · ring
  · rw [← hE]; ring

lemma threeTermQuotient_order_ge (he : SigmaEntire) {z : ℂ} {k m1 m2 m3 : ℤ}
    (h1 : meromorphicOrderAt (fun w => wSigma L (w + (b + c))) z = (m1 : WithTop ℤ))
    (h2 : meromorphicOrderAt (fun w => wSigma L (w + -b)) z = (m2 : WithTop ℤ))
    (h3 : meromorphicOrderAt (fun w => wSigma L (w + -c)) z = (m3 : WithTop ℤ))
    (hN : ((k + (m1 + m2 + m3) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (nAux L b c) z) :
    (k : WithTop ℤ) ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by
  have hm : meromorphicOrderAt (threeTermDenom L b c) z = ((m1 + m2 + m3 : ℤ) : WithTop ℤ) := by
    have e : threeTermDenom L b c = ((fun w => wSigma L (w + (b + c))) * (fun w => wSigma L (w + -b)))
        * (fun w => wSigma L (w + -c)) := rfl
    rw [e, meromorphicOrderAt_mul ((sig_analyticAt L he (b + c) z).mul
        (sig_analyticAt L he (-b) z)).meromorphicAt (sig_analyticAt L he (-c) z).meromorphicAt,
      meromorphicOrderAt_mul (sig_analyticAt L he (b + c) z).meromorphicAt
        (sig_analyticAt L he (-b) z).meromorphicAt, h1, h2, h3]
    rfl
  unfold threeTermQuotient
  rw [fun_meromorphicOrderAt_div (threeTermNum_meromorphicAt L b c he z)
    (threeTermDenom_analyticAt L b c he z).meromorphicAt, hm]
  exact le_sub_of_add_le hN

lemma one_le_order {f : ℂ → ℂ} {z : ℂ} (han : AnalyticAt ℂ f z) (h0 : f z = 0) :
    ((1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f z := by
  rw [han.meromorphicOrderAt_eq]
  refine ENat.monotone_map_iff.mpr Nat.mono_cast
    ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 1) han).mpr fun i hi ↦ ?_)
  interval_cases i
  simpa using h0

lemma threeTermNum_eq_zero_left {z : ℂ} (h : z + -b ∈ L.lattice) : nAux L b c z = 0 := by
  obtain ⟨h1, h2⟩ := wp_congr L h
  unfold nAux threeTermDet
  rw [h1, h2]; ring

lemma threeTermNum_eq_zero_right {z : ℂ} (h : z + -c ∈ L.lattice) : nAux L b c z = 0 := by
  obtain ⟨h1, h2⟩ := wp_congr L h
  unfold nAux threeTermDet
  rw [h1, h2]; ring

lemma threeTermQuotient_order_off (he : SigmaEntire) (hord : SigmaOrder) (hm : b - c ∉ L.lattice) {z : ℂ}
    (hzL : z ∉ L.lattice) {m1 : ℤ}
    (h1 : meromorphicOrderAt (fun w => wSigma L (w + (b + c))) z = (m1 : WithTop ℤ)) :
    ((-m1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by
  have han := threeTermNum_analyticAt L b c he z hzL
  by_cases hb : z + -b ∈ L.lattice
  · have hc : z + -c ∉ L.lattice := fun hc => hm (by
      have := L.lattice.sub_mem hc hb
      convert this using 1; ring)
    refine threeTermQuotient_order_ge L b c he h1 (sig_order_mem L hord hb) (sig_order_notMem L hord hc) ?_
    have := one_le_order han (threeTermNum_eq_zero_left L b c hb)
    convert this using 2; ring
  · by_cases hc : z + -c ∈ L.lattice
    · refine threeTermQuotient_order_ge L b c he h1 (sig_order_notMem L hord hb) (sig_order_mem L hord hc) ?_
      have := one_le_order han (threeTermNum_eq_zero_right L b c hc)
      convert this using 2; ring
    · refine threeTermQuotient_order_ge L b c he h1 (sig_order_notMem L hord hb) (sig_order_notMem L hord hc) ?_
      have := han.meromorphicOrderAt_nonneg
      convert this using 1
      simp

lemma threeTermQuotient_order_zero (he : SigmaEntire) (hz : SigmaZero) (hord : SigmaOrder)
    (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) :
    0 ≤ meromorphicOrderAt (threeTermQuotient L b c) 0 := by
  have hN : 0 ≤ meromorphicOrderAt (nAux L b c) 0 := by
    have : nAux L b c =ᶠ[𝓝[≠] 0] frobeniusStickelbergerDetMulSigmaCube L b c := by
      filter_upwards [self_mem_nhdsWithin] with x hx using threeTermNum_eq_twistedGamma_of_sigmaZero L b c hz x hx
    rw [meromorphicOrderAt_congr this]
    exact (twistedGamma_analyticAt_zero L b c he).meromorphicOrderAt_nonneg
  have := threeTermQuotient_order_ge L b c he (z := 0) (k := 0)
    (sig_order_notMem L hord (by simpa using hp))
    (sig_order_notMem L hord (by simpa using hb))
    (sig_order_notMem L hord (by simpa using hc)) (by simpa using hN)
  simpa using this

lemma threeTermQuotient_order_lattice (he : SigmaEntire) (hz : SigmaZero) (hord : SigmaOrder) (hq : SigmaQuasi)
    (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) {z : ℂ}
    (hzL : z ∈ L.lattice) : 0 ≤ meromorphicOrderAt (threeTermQuotient L b c) z := by
  have h := meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt (x := 0) (c := z)
    (f := threeTermQuotient L b c)
  have h' : threeTermQuotient L b c ∘ (· + z) = threeTermQuotient L b c := funext fun x => threeTermQuotient_periodic L b c hq z hzL x
  rw [h', zero_add] at h
  rw [← h]
  exact threeTermQuotient_order_zero L b c he hz hord hb hc hp

lemma core (h1 : EllipticOnePole) (hord : SigmaOrder) (hq : SigmaQuasi) (hz : SigmaZero)
    (he : SigmaEntire) (ho : SigmaOdd) (hs : SigmaSimple) (hadd : SigmaAdd) {a : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice)
    (hm : b - c ∉ L.lattice) :
    threeTermDet L b c a * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a) := by
  obtain ⟨k, hk⟩ := h1 L (threeTermQuotient L b c) (-(b + c)) (threeTermQuotient_meromorphicAt L b c he)
    (threeTermQuotient_periodic L b c hq)
    (fun z hzp => by
      by_cases hzL : z ∈ L.lattice
      · exact threeTermQuotient_order_lattice L b c he hz hord hq hb hc hp hzL
      · have := threeTermQuotient_order_off L b c he hord hm hzL
          (sig_order_notMem L hord (β := b + c) (by rwa [sub_neg_eq_add] at hzp))
        simpa using this)
    (by
      have hpL : -(b + c) ∉ L.lattice := fun h => hp (by simpa using L.lattice.neg_mem h)
      have := threeTermQuotient_order_off L b c he hord hm hpL
        (sig_order_mem L hord (β := b + c) (by simp))
      simpa using this)
  have hev : ∀ z, ∀ᶠ x in 𝓝[≠] z, nAux L b c x = k * threeTermDenom L b c x := by
    intro z
    filter_upwards [eventually_notMem L z, threeTermDenom_eventually_ne L b c he hord z] with x hx1 hx2
    have := hk x ((threeTermNum_analyticAt L b c he x hx1).div (threeTermDenom_analyticAt L b c he x) hx2).continuousAt
    unfold threeTermQuotient at this
    rw [div_eq_iff hx2] at this
    exact this
  have hmc : ∀ z, ContinuousAt (fun x => k * threeTermDenom L b c x) z := fun z =>
    continuousAt_const.mul (threeTermDenom_analyticAt L b c he z).continuousAt
  have h0 : frobeniusStickelbergerDetMulSigmaCube L b c 0 = k * threeTermDenom L b c 0 := by
    refine eq_of_eventuallyEq_punctured (g := fun x => k * threeTermDenom L b c x)
      (twistedGamma_analyticAt_zero L b c he).continuousAt (hmc 0) ?_
    filter_upwards [hev 0, self_mem_nhdsWithin] with x hx1 hx2
    rw [← threeTermNum_eq_twistedGamma_of_sigmaZero L b c hz x hx2, hx1]
  have ha' : nAux L b c a = k * threeTermDenom L b c a :=
    eq_of_eventuallyEq_punctured (g := fun x => k * threeTermDenom L b c x)
      (threeTermNum_analyticAt L b c he a ha).continuousAt (hmc a) (hev a)
  have hS : wSigma L (b + c) ≠ 0 := fun h => hp ((hz L _).1 h)
  have h3 := hadd L b c hb hc
  rw [twistedGamma_zero L b c hz hs] at h0
  unfold threeTermDenom at h0 ha'
  unfold nAux at ha'
  rw [zero_add, zero_add, zero_add, ho L b, ho L c] at h0
  have e1 : a + (b + c) = a + b + c := by ring
  have e2 : a + -b = a - b := by ring
  have e3 : wSigma L (a + -c) = -wSigma L (c - a) := by rw [← ho L]; congr 1; ring
  rw [e1, e2, e3] at ha'
  refine mul_left_cancel₀ hS ?_
  linear_combination (wSigma L (b + c) * wSigma L b ^ 3 * wSigma L c ^ 3) * ha'
    + (wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (c - a) * wSigma L b ^ 2 * wSigma L c ^ 2) * h0
    - (2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (c - a)) * h3

lemma trivial_case (hz : SigmaZero) {a : ℂ} (hm : b - c ∈ L.lattice) :
    threeTermDet L b c a * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a) := by
  obtain ⟨h1, h2⟩ := wp_congr L (x := b) (y := c) (by simpa [sub_eq_add_neg] using hm)
  rw [(hz L (b - c)).2 hm]
  unfold threeTermDet
  rw [h1, h2]; ring

lemma step (h1 : EllipticOnePole) (hord : SigmaOrder) (hq : SigmaQuasi) (hz : SigmaZero)
    (he : SigmaEntire) (ho : SigmaOdd) (hs : SigmaSimple) (hadd : SigmaAdd) {a : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (hc : c ∉ L.lattice) (hp : b + c ∉ L.lattice) :
    threeTermDet L b c a * (wSigma L a * wSigma L b * wSigma L c) ^ 3
      = 2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a) := by
  by_cases hm : b - c ∈ L.lattice
  · exact trivial_case L b c hz hm
  · exact core L b c h1 hord hq hz he ho hs hadd ha hb hc hp hm

lemma det_eq (a : ℂ) :
    Matrix.det !![1, L.weierstrassP a, L.derivWeierstrassP a;
                  1, L.weierstrassP b, L.derivWeierstrassP b;
                  1, L.weierstrassP c, L.derivWeierstrassP c] = threeTermDet L b c a := by
  rw [Matrix.det_fin_three]
  simp [threeTermDet]
  ring

lemma threeTermDet_cycle (a : ℂ) : threeTermDet L b c a = threeTermDet L c a b := by
  unfold threeTermDet; ring

end ThreeTermRelation

open ThreeTermRelation in
theorem sigmaThree_of (h1 : EllipticOnePole) (hord : SigmaOrder) (hq : SigmaQuasi) (hz : SigmaZero)
    (he : SigmaEntire) (ho : SigmaOdd) (hs : SigmaSimple) (hadd : SigmaAdd) : SigmaThree := by
  intro L a b c ha hb hc
  rw [det_eq]
  by_cases hp1 : b + c ∈ L.lattice
  · by_cases hp2 : c + a ∈ L.lattice
    · have hm : a - b ∈ L.lattice := by
        have := L.lattice.sub_mem hp2 hp1
        convert this using 1; ring
      have := trivial_case L a b hz (a := c) hm
      rw [threeTermDet_cycle, threeTermDet_cycle]
      have e : c + a + b = a + b + c := by ring
      rw [e] at this
      linear_combination this
    · have := step L c a h1 hord hq hz he ho hs hadd hb hc ha hp2
      rw [threeTermDet_cycle]
      have e : b + c + a = a + b + c := by ring
      rw [e] at this
      linear_combination this
  · exact step L b c h1 hord hq hz he ho hs hadd ha hb hc hp1

theorem sgStarThree_of (h : SigmaThree) : SgStarThree := by
  intro L a b c ha hb hc
  have h0 := h L a b c ha hb hc
  have hexp : (Complex.exp (-(s2 L) * a ^ 2 / 2) * Complex.exp (-(s2 L) * b ^ 2 / 2)
        * Complex.exp (-(s2 L) * c ^ 2 / 2)) ^ 3
      = Complex.exp (-(s2 L) * (a + b + c) ^ 2 / 2) * Complex.exp (-(s2 L) * (a - b) ^ 2 / 2)
        * Complex.exp (-(s2 L) * (b - c) ^ 2 / 2) * Complex.exp (-(s2 L) * (c - a) ^ 2 / 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_nat_mul, ← Complex.exp_add,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1; push_cast; ring
  unfold sgStar
  generalize Matrix.det !![1, L.weierstrassP a, L.derivWeierstrassP a;
                   1, L.weierstrassP b, L.derivWeierstrassP b;
                   1, L.weierstrassP c, L.derivWeierstrassP c] = D at h0 ⊢
  linear_combination (Complex.exp (-(s2 L) * a ^ 2 / 2) * Complex.exp (-(s2 L) * b ^ 2 / 2)
        * Complex.exp (-(s2 L) * c ^ 2 / 2)) ^ 3 * h0
    + (2 * wSigma L (a + b + c) * wSigma L (a - b) * wSigma L (b - c) * wSigma L (c - a)) * hexp

open ThreeTermRelation in
theorem thetaLine_of (h1 : EllipticOnePole) (hq : SgStarQuasi) (hb : SgStarBasic) : ThetaLine := by
  intro L F hF hfe
  obtain ⟨hd, -, hzero, hder, -⟩ := hb L
  have hmer : ∀ z, MeromorphicAt (fun z => F z / sgStar L z) z := fun z =>
    (hF.analyticAt z).meromorphicAt.div (hd.analyticAt z).meromorphicAt
  have hper : IsPeriodic L (fun z => F z / sgStar L z) := by
    intro ω hω z
    have e1 := hfe ω hω z
    have e2 := hq L ω z hω
    have e3 := semiChar_mul_self L ω
    have hχ : (semiChar L ω)⁻¹ = semiChar L ω := inv_eq_of_mul_eq_one_left e3
    unfold opU at e1
    have hE : Complex.exp (-(Real.pi : ℂ) * herm L z ω - (Real.pi : ℂ) * herm L ω ω / 2)
        = (Complex.exp ((Real.pi : ℂ) * herm L z ω + (Real.pi : ℂ) * herm L ω ω / 2))⁻¹ := by
      rw [← Complex.exp_neg]; congr 1; ring
    rw [hE] at e1
    show F (z + ω) / sgStar L (z + ω) = F z / sgStar L z
    rw [e2, ← e1, div_eq_mul_inv, div_eq_mul_inv, mul_inv, mul_inv, hχ]
    ring
  have han : ∀ z, z ∉ L.lattice → AnalyticAt ℂ (fun z => F z / sgStar L z) z := fun z hz =>
    (hF.analyticAt z).div (hd.analyticAt z) (fun h => hz ((hzero z).1 h))
  have hord0 : meromorphicOrderAt (sgStar L) 0 = 1 := by
    rw [(hd.analyticAt 0).meromorphicOrderAt_eq,
      (hd.analyticAt 0).analyticOrderAt_eq_one_of_zero_deriv_ne_zero ((hzero 0).2 (zero_mem _))
        (by rw [hder]; exact one_ne_zero)]
    rfl
  obtain ⟨c, hc⟩ := h1 L (fun z => F z / sgStar L z) 0 hmer hper
    (fun z hz => (han z (by simpa using hz)).meromorphicOrderAt_nonneg) (by
      have hF0 := (hF.analyticAt 0).meromorphicOrderAt_nonneg
      rw [fun_meromorphicOrderAt_div (hF.analyticAt 0).meromorphicAt (hd.analyticAt 0).meromorphicAt,
        hord0]
      have := le_sub_of_add_le (o := meromorphicOrderAt F 0) (m := 1) (k := -1) (by simpa using hF0)
      simpa using this)
  have hoff : ∀ z, z ∉ L.lattice → F z = c * sgStar L z := by
    intro z hz
    have := hc z (han z hz).continuousAt
    have hne : sgStar L z ≠ 0 := fun h => hz ((hzero z).1 h)
    field_simp at this
    rw [this, mul_comm]
  refine ⟨c, fun z => ?_⟩
  refine eq_of_eventuallyEq_punctured (f := F) (g := fun z => c * sgStar L z)
    hF.continuous.continuousAt (continuous_const.mul hd.continuous).continuousAt ?_
  filter_upwards [eventually_notMem L z] with x hx using hoff x hx

end Formalism.L2.Th1.F
