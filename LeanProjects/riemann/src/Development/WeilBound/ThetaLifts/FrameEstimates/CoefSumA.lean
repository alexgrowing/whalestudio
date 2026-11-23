import Mathlib

noncomputable section

open MeasureTheory Topology Filter
open scoped ENNReal ComplexConjugate Pointwise

namespace PositivityTheory.ThKEst.CS

variable {G Γ : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [AddCommGroup Γ]

structure Dual (r : Γ →+ G) (e : Γ → G → ℂ) : Prop where
  inj : Function.Injective r
  cont : ∀ ξ, Continuous (e ξ)
  norm : ∀ ξ u, ‖e ξ u‖ = 1
  addl : ∀ ξ η u, e (ξ + η) u = e ξ u * e η u
  addr : ∀ ξ u v, e ξ (u + v) = e ξ u * e ξ v
  triv : ∀ ξ η, e ξ (r η) = 1
  sep : ∀ u, (∀ ξ, e ξ u = 1) → u ∈ r.range
  nondeg : ∀ ξ, ξ ≠ 0 → ∃ u, e ξ u ≠ 1
  cpt : ∃ K : Set G, IsCompact K ∧ ∀ u, ∃ ξ, u - r ξ ∈ K

variable {r : Γ →+ G} {e : Γ → G → ℂ}

omit [IsTopologicalAddGroup G] in
theorem Dual.ne (h : Dual r e) (ξ u) : e ξ u ≠ 0 := fun h0 => by
  have := h.norm ξ u
  rw [h0, norm_zero] at this
  exact zero_ne_one this

omit [IsTopologicalAddGroup G] in
theorem Dual.zero (h : Dual r e) (u) : e 0 u = 1 := by
  have := h.addl 0 0 u
  rw [add_zero] at this
  exact (mul_eq_left₀ (h.ne 0 u)).1 this.symm

omit [IsTopologicalAddGroup G] in
theorem Dual.zero' (h : Dual r e) (ξ) : e ξ 0 = 1 := by
  simpa using h.triv ξ 0

omit [IsTopologicalAddGroup G] in
theorem Dual.conj (h : Dual r e) (ξ u) : conj (e ξ u) = e (-ξ) u := by
  have h1 : e ξ u * e (-ξ) u = 1 := by rw [← h.addl, add_neg_cancel, h.zero]
  have h2 : e ξ u * conj (e ξ u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h.norm]; simp
  exact mul_left_cancel₀ (h.ne ξ u) (h2.trans h1.symm)

omit [IsTopologicalAddGroup G] in
theorem Dual.per (h : Dual r e) (ξ η u) : e ξ (r η + u) = e ξ u := by
  rw [h.addr, h.triv, one_mul]

def liftC (f : G → ℂ) (hf : ∀ ξ u, f (r ξ + u) = f u) (hc : Continuous f) : C(G ⧸ r.range, ℂ) :=
  ⟨Quotient.lift f (by
    intro x y hxy
    obtain ⟨ξ, hξ⟩ : -x + y ∈ r.range := QuotientAddGroup.leftRel_apply.1 hxy
    have := hf ξ x
    rw [hξ, show -x + y + x = y by abel] at this
    exact this.symm), hc.quotient_lift _⟩

def chiC (h : Dual r e) (ξ : Γ) : C(G ⧸ r.range, ℂ) := liftC (e ξ) (h.per ξ) (h.cont ξ)

omit [IsTopologicalAddGroup G] in
theorem chiC_apply (h : Dual r e) (ξ : Γ) (u : G) : chiC h ξ (u : G ⧸ r.range) = e ξ u := rfl

omit [IsTopologicalAddGroup G] in
theorem chiC_mul (h : Dual r e) (ξ η : Γ) : chiC h ξ * chiC h η = chiC h (ξ + η) := by
  ext q
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ContinuousMap.mul_apply, chiC_apply, h.addl]

omit [IsTopologicalAddGroup G] in
theorem chiC_zero (h : Dual r e) : chiC h 0 = 1 := by
  ext q
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ContinuousMap.one_apply, chiC_apply, h.zero]

omit [IsTopologicalAddGroup G] in
theorem chiC_star (h : Dual r e) (ξ : Γ) : star (chiC h ξ) = chiC h (-ξ) := by
  ext q
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [ContinuousMap.star_apply, chiC_apply, chiC_apply]
  exact h.conj ξ u

def Achar (h : Dual r e) : StarSubalgebra ℂ C(G ⧸ r.range, ℂ) where
  carrier := Submodule.span ℂ (Set.range (chiC h))
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  mul_mem' := by
    intro f g hf hg
    induction hf using Submodule.span_induction with
    | mem x hx =>
      induction hg using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨ξ, rfl⟩ := hx
        obtain ⟨η, rfl⟩ := hy
        rw [chiC_mul]
        exact Submodule.subset_span ⟨ξ + η, rfl⟩
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add y y' _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
      | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
    | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h
  one_mem' := by
    rw [← chiC_zero h]; exact Submodule.subset_span ⟨0, rfl⟩
  algebraMap_mem' := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, ← chiC_zero h]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, rfl⟩)
  star_mem' := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ξ, rfl⟩ := hx
      rw [chiC_star]; exact Submodule.subset_span ⟨-ξ, rfl⟩
    | zero => rw [star_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [star_add]; exact Submodule.add_mem _ h1 h2
    | smul c x _ h => rw [star_smul]; exact Submodule.smul_mem _ _ h

omit [IsTopologicalAddGroup G] in
theorem Dual.compactQ (h : Dual r e) : CompactSpace (G ⧸ r.range) := by
  obtain ⟨K, hK, hKc⟩ := h.cpt
  refine ⟨?_⟩
  have h : (Set.univ : Set (G ⧸ r.range)) = (QuotientAddGroup.mk : G → G ⧸ r.range) '' K := by
    ext q
    simp only [Set.mem_univ, Set.mem_image, true_iff]
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨ξ, hξ⟩ := hKc z
    refine ⟨z - r ξ, hξ, ?_⟩
    rw [QuotientAddGroup.eq, show -(z - r ξ) + z = r ξ by abel]
    exact ⟨ξ, rfl⟩
  rw [h]
  exact hK.image continuous_quotient_mk'

omit [IsTopologicalAddGroup G] in
theorem Dual.separates (h : Dual r e) : (Achar h).SeparatesPoints := by
  intro q q' hqq'
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨x', rfl⟩ := QuotientAddGroup.mk_surjective q'
  obtain ⟨ξ, hξ⟩ : ∃ ξ, e ξ (-x + x') ≠ 1 := by
    by_contra h'
    push Not at h'
    exact hqq' (QuotientAddGroup.eq.2 (h.sep _ h'))
  refine ⟨chiC h ξ, ⟨chiC h ξ, Submodule.subset_span ⟨ξ, rfl⟩, rfl⟩, fun heq => hξ ?_⟩
  have h1 : e ξ x = e ξ x' := heq
  have h2 := h.addr ξ x (-x + x')
  rw [show x + (-x + x') = x' by abel, ← h1] at h2
  exact (mul_eq_left₀ (h.ne ξ x)).1 h2.symm

omit [IsTopologicalAddGroup G] in
theorem Dual.bdd (h : Dual r e) {g : G → ℂ} (hg : Continuous g) (hp : ∀ ξ u, g (r ξ + u) = g u) :
    ∃ C, ∀ u, ‖g u‖ ≤ C := by
  obtain ⟨K, hK, hKc⟩ := h.cpt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun u => ?_⟩
  obtain ⟨ξ, hξ⟩ := hKc u
  have e : g u = g (u - r ξ) := by rw [← hp ξ (u - r ξ), add_sub_cancel]
  rw [e]
  exact hC _ hξ

variable [MeasurableSpace G] [BorelSpace G] [Countable Γ] {μ : Measure G} [μ.IsAddHaarMeasure] {D : Set G}

instance countable_range (r : Γ →+ G) : Countable r.range := r.rangeRestrict_surjective.countable

instance mcv (Λ : AddSubgroup G) : MeasurableConstVAdd Λ G :=
  ⟨fun c => (continuous_const.add continuous_id : Continuous fun x : G => (c : G) + x).measurable⟩

instance viv (Λ : AddSubgroup G) : VAddInvariantMeasure Λ G μ :=
  ⟨fun c s _ => measure_preimage_add μ (c : G) s⟩

theorem Dual.lint (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) (f : G → ℝ≥0∞) :
    ∫⁻ u, f u ∂μ = ∑' ξ, ∫⁻ u in D, f (r ξ + u) ∂μ := by
  rw [hD.lintegral_eq_tsum'' f, ← (AddMonoidHom.ofInjective h.inj).toEquiv.tsum_eq]
  rfl

theorem Dual.fin (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) : μ D ≠ ∞ := by
  obtain ⟨K, hK, hKc⟩ := h.cpt
  have hK' := hK.closure
  have hm : MeasurableSet (closure K) := isClosed_closure.measurableSet
  have h1 := h.lint hD ((closure K).indicator 1)
  have hmeas : ∀ ξ, AEMeasurable (fun u => (closure K).indicator (1 : G → ℝ≥0∞) (r ξ + u)) (μ.restrict D) := fun ξ =>
    ((measurable_one.indicator hm).comp (measurable_const_add _)).aemeasurable
  rw [lintegral_indicator_one hm, ← lintegral_tsum hmeas] at h1
  refine ne_top_of_le_ne_top (hK'.measure_lt_top (μ := μ)).ne ?_
  rw [h1, ← setLIntegral_one]
  refine lintegral_mono fun u => ?_
  obtain ⟨ξ, hξ⟩ := hKc u
  refine le_trans ?_ (ENNReal.le_tsum (-ξ))
  have : r (-ξ) + u ∈ closure K := subset_closure (by rwa [map_neg, neg_add_eq_sub])
  simp [Set.indicator_of_mem this, ← map_neg, -map_neg]

theorem Dual.intOn (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) {g : G → ℂ} (hg : Continuous g)
    (hp : ∀ ξ u, g (r ξ + u) = g u) : IntegrableOn g D μ := by
  obtain ⟨C, hC⟩ := h.bdd hg hp
  exact Measure.integrableOn_of_bounded (h.fin hD) hg.aestronglyMeasurable (M := C) (Eventually.of_forall hC)

theorem Dual.eq_zero (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) {P : G → ℂ} (hPc : Continuous P)
    (hPp : ∀ ξ u, P (r ξ + u) = P u) (hcoef : ∀ ξ, ∫ u in D, e ξ u * P u ∂μ = 0) : P = 0 := by
  have := h.compactQ
  have hDf := h.fin hD
  obtain ⟨C, hC⟩ := h.bdd hPc hPp
  have hint : ∀ g : C(G ⧸ r.range, ℂ), IntegrableOn (fun u : G => g (u : G ⧸ r.range) * P u) D μ := fun g =>
    h.intOn hD ((g.continuous.comp continuous_quotient_mk').mul hPc) fun ξ u => by
      rw [hPp]
      congr 2
      rw [QuotientAddGroup.eq, show -(r ξ + u) + u = -r ξ by abel]
      exact neg_mem ⟨ξ, rfl⟩
  let L₀ : C(G ⧸ r.range, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun g => ∫ u in D, g (u : G ⧸ r.range) * P u ∂μ
      map_add' := fun x y => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (hint x) (hint y)
      map_smul' := fun c x => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
        exact integral_const_mul _ _ }
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  let L : C(G ⧸ r.range, ℂ) →L[ℂ] ℂ := L₀.mkContinuous (C * μ.real D) fun g => by
    refine (norm_setIntegral_le_of_norm_le_const (C := ‖g‖ * C) hDf.lt_top fun u _ => ?_).trans (le_of_eq (by ring))
    rw [norm_mul]
    exact mul_le_mul (g.norm_coe_le_norm _) (hC u) (norm_nonneg _) (norm_nonneg _)
  have hvan : (Achar h : Set C(G ⧸ r.range, ℂ)) ⊆ {g | L g = 0} := by
    intro g hg
    have : Submodule.span ℂ (Set.range (chiC h)) ≤ LinearMap.ker L₀ :=
      Submodule.span_le.2 (by rintro _ ⟨ξ, rfl⟩; exact hcoef ξ)
    exact this hg
  have hclos := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (Achar h) h.separates
  let Pb : C(G ⧸ r.range, ℂ) := liftC (fun u => conj (P u)) (fun ξ u => by rw [hPp]) (Complex.continuous_conj.comp hPc)
  have hmem : Pb ∈ closure ((Achar h : Set C(G ⧸ r.range, ℂ))) := by
    have : Pb ∈ (Achar h).topologicalClosure := by rw [hclos]; exact StarSubalgebra.mem_top
    exact this
  have hint0 : ∫ u in D, conj (P u) * P u ∂μ = 0 :=
    closure_minimal hvan (isClosed_eq L.continuous continuous_const) hmem
  have hsq : ∫ u in D, ‖P u‖ ^ 2 ∂μ = 0 := by
    have e : (fun u => conj (P u) * P u) = fun u => ((‖P u‖ ^ 2 : ℝ) : ℂ) := by
      funext u; rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e, integral_complex_ofReal] at hint0
    exact_mod_cast hint0
  have hInt : IntegrableOn (fun u => ‖P u‖ ^ 2) D μ := by
    refine Measure.integrableOn_of_bounded hDf (hPc.norm.pow 2).aestronglyMeasurable (M := C ^ 2)
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC u) 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun u => by positivity) hInt).1 hsq
  have h0 : ∫⁻ u, ‖P u‖ₑ ∂μ = 0 := by
    rw [h.lint hD]
    simp only [hPp]
    have : ∫⁻ u in D, ‖P u‖ₑ ∂μ = 0 := by
      rw [← lintegral_zero (μ := μ.restrict D)]
      refine lintegral_congr_ae (hae.mono fun u hu => ?_)
      simpa using hu
    simp [this]
  rw [lintegral_eq_zero_iff hPc.enorm.measurable] at h0
  refine (hPc.ae_eq_iff_eq μ continuous_zero).1 (h0.mono fun u hu => ?_)
  simpa using hu

theorem Dual.orth (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) {ξ : Γ} (hξ : ξ ≠ 0) :
    ∫ u in D, e ξ u ∂μ = 0 := by
  obtain ⟨u₀, hu₀⟩ := h.nondeg ξ hξ
  have hD' := hD.vadd_of_comm u₀
  have h1 := hD.setIntegral_eq hD' (f := e ξ) (fun g s => by
    obtain ⟨_, η, rfl⟩ := g
    exact h.per ξ η s)
  have h2 := (measurePreserving_add_left μ u₀).setIntegral_image_emb (measurableEmbedding_addLeft u₀) (e ξ) D
  have e' : u₀ +ᵥ D = (fun s => u₀ + s) '' D := rfl
  rw [e', h2] at h1
  simp only [h.addr] at h1
  rw [integral_const_mul] at h1
  by_contra hne
  exact hu₀ ((mul_eq_right₀ hne).1 h1.symm)

theorem Dual.series (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) {P : G → ℂ} (hP : Continuous P)
    (hper : ∀ ξ u, P (r ξ + u) = P u) {c : Γ → ℂ} (hc : ∀ ξ, ∫ u in D, e ξ u * P u ∂μ = c ξ)
    (hsum : Summable fun ξ => ‖c ξ‖) : (μ.real D : ℂ) * P 0 = ∑' ξ, c ξ := by
  classical
  set S : G → ℂ := fun u => ∑' ξ, c ξ * e (-ξ) u with hSdef
  have hS : Continuous S := continuous_tsum (fun ξ => continuous_const.mul (h.cont _)) hsum
    (fun ξ u => by simp [h.norm])
  have hSper : ∀ η u, S (r η + u) = S u := fun η u => by simp only [hSdef, h.per]
  have hcoefS : ∀ ξ, ∫ u in D, e ξ u * S u ∂μ = μ.real D * c ξ := by
    intro ξ
    have hsw : ∀ u, e ξ u * S u = ∑' ξ', c ξ' * e (ξ - ξ') u := by
      intro u
      simp only [hSdef, ← tsum_mul_left, sub_eq_add_neg, h.addl]
      exact tsum_congr fun _ => by ring
    simp_rw [hsw]
    have hInt : ∀ ξ', Integrable (fun u => c ξ' * e (ξ - ξ') u) (μ.restrict D) :=
      fun ξ' => h.intOn hD (continuous_const.mul (h.cont _)) fun η u => by rw [h.per]
    have hnorm : ∀ ξ', ∫ u in D, ‖c ξ' * e (ξ - ξ') u‖ ∂μ = μ.real D * ‖c ξ'‖ := by
      intro ξ'
      simp [h.norm]
    rw [← integral_tsum_of_summable_integral_norm hInt (by simp_rw [hnorm]; exact hsum.mul_left _)]
    rw [tsum_eq_single ξ]
    · simp [h.zero]
    · intro ξ' hne
      rw [integral_const_mul, h.orth hD (sub_ne_zero.2 hne.symm), mul_zero]
  have hQ := h.eq_zero hD (P := fun u => (μ.real D : ℂ) * P u - S u) ((continuous_const.mul hP).sub hS)
    (fun ξ u => by simp only [hper, hSper]) fun ξ => by
      have h1 : IntegrableOn (fun u => (μ.real D : ℂ) * (e ξ u * P u)) D μ :=
        h.intOn hD (continuous_const.mul ((h.cont ξ).mul hP)) fun η u => by rw [h.per, hper]
      have h2 : IntegrableOn (fun u => e ξ u * S u) D μ :=
        h.intOn hD ((h.cont ξ).mul hS) fun η u => by rw [h.per, hSper]
      have e1 : ∀ u, e ξ u * ((μ.real D : ℂ) * P u - S u) = (μ.real D : ℂ) * (e ξ u * P u) - e ξ u * S u :=
        fun u => by ring
      simp only [e1]
      rw [integral_sub h1 h2, integral_const_mul, hc, hcoefS, sub_self]
  have := congrFun hQ 0
  simp only [Pi.zero_apply, sub_eq_zero] at this
  rw [this]
  simp [hSdef, h.zero']

theorem Dual.poisson_le [LocallyCompactSpace G] (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) :
    ∃ c : ℝ, 0 < c ∧ ∀ H : G → ℂ, Continuous H →
      (∀ K : Set G, IsCompact K → ∃ b : Γ → ℝ, Summable b ∧ ∀ ξ, ∀ a ∈ K, ‖H (r ξ + a)‖ ≤ b ξ) →
      ‖∑' ξ, H (r ξ)‖ₑ ≤ ENNReal.ofReal c * ∑' ξ, ‖∫ u, e ξ u * H u ∂μ‖ₑ := by
  have hDf := h.fin hD
  have hm : 0 < μ.real D := ENNReal.toReal_pos (hD.measure_ne_zero (NeZero.ne μ)) hDf
  refine ⟨(μ.real D)⁻¹, inv_pos.2 hm, fun H hH hb => ?_⟩
  set c : Γ → ℂ := fun ξ => ∫ u, e ξ u * H u ∂μ with hcdef
  by_cases htop : ∑' ξ, ‖c ξ‖ₑ = ∞
  · rw [htop, ENNReal.mul_top (by simpa using hm)]
    exact le_top
  have hsum : Summable fun ξ => ‖c ξ‖ := by
    have := ENNReal.summable_toReal htop
    simpa using this
  set P : G → ℂ := fun u => ∑' ξ, H (r ξ + u) with hP
  have hper : ∀ ξ u, P (r ξ + u) = P u := by
    intro ξ u
    simp only [hP]
    refine Eq.trans (tsum_congr fun η => ?_) ((Equiv.addRight ξ).tsum_eq (fun η => H (r η + u)))
    simp [add_assoc]
  have hT : ∀ ξ, Continuous fun u => H (r ξ + u) := fun ξ => hH.comp (continuous_const.add continuous_id)
  have hPc : Continuous P := by
    rw [continuous_iff_continuousAt]
    intro w
    obtain ⟨N, hN, hNw⟩ := exists_compact_mem_nhds w
    obtain ⟨b, hb1, hb2⟩ := hb N hN
    exact (continuousOn_tsum (fun ξ => (hT ξ).continuousOn) hb1 hb2).continuousAt hNw
  have hfin : ∑' ξ, ∫⁻ u in D, ‖H (r ξ + u)‖ₑ ∂μ ≠ ∞ := by
    obtain ⟨K, hK, hKc⟩ := h.cpt
    obtain ⟨b, hb1, hb2⟩ := hb K hK
    obtain ⟨ξ₀, hξ₀⟩ := hKc 0
    have hb0 : ∀ ξ, 0 ≤ b ξ := fun ξ => (norm_nonneg _).trans (hb2 ξ _ hξ₀)
    rw [← lintegral_tsum fun ξ => (hT ξ).enorm.measurable.aemeasurable]
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in D, ENNReal.ofReal (∑' ξ, b ξ) ∂μ) ?_ (lintegral_mono fun u => ?_)
    · rw [setLIntegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hDf
    · obtain ⟨η, hη⟩ := hKc u
      rw [ENNReal.ofReal_tsum_of_nonneg hb0 hb1, ← (Equiv.addRight η).tsum_eq (fun ξ => ENNReal.ofReal (b ξ))]
      refine ENNReal.tsum_le_tsum fun ξ => ?_
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hb2 (ξ + η) _ hη
      rwa [map_add, show r ξ + r η + (u - r η) = r ξ + u by abel] at this
  have hcoef : ∀ ξ, ∫ u in D, e ξ u * P u ∂μ = c ξ := by
    intro ξ
    have hgn : ∀ u v, ‖e ξ u * H v‖ₑ = ‖H v‖ₑ := fun u v => by
      rw [← ofReal_norm, ← ofReal_norm, norm_mul, h.norm, one_mul]
    have hgi : Integrable (fun u => e ξ u * H u) μ := by
      refine ⟨((h.cont ξ).mul hH).aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      simp only [hgn]
      rw [h.lint hD]
      exact hfin.lt_top
    simp only [hcdef]
    rw [hD.integral_eq_tsum'' _ hgi, ← (AddMonoidHom.ofInjective h.inj).toEquiv.tsum_eq]
    have hv : ∀ η u, ((AddMonoidHom.ofInjective h.inj).toEquiv η +ᵥ u : G) = r η + u := fun η u => rfl
    simp only [hv, h.per, hP, ← tsum_mul_left]
    refine integral_tsum (fun η => ((h.cont ξ).mul (hT η)).aestronglyMeasurable) ?_
    simpa only [hgn] using hfin
  have key := h.series hD hPc hper hcoef hsum
  have h0 : ∑' ξ, H (r ξ) = ((μ.real D)⁻¹ : ℝ) * ∑' ξ, c ξ := by
    rw [← key, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hm.ne']
    simp [hP]
  rw [h0, enorm_mul]
  refine mul_le_mul' (le_of_eq ?_) (enorm_tsum_le_tsum_enorm)
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (inv_pos.2 hm).le]

end PositivityTheory.ThKEst.CS

end
