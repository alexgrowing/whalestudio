import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Pointwise

namespace GlobalTheory.SeparatingCharacters

theorem tsum_coefficients_eq_value_zero : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → (∀ a, (∀ x, χ a x = 1) → a = 0) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → Summable (fun a => ∫ x in 𝓕, χ a x * Φ x ∂μ) → ∑' a, ∫ x in 𝓕, χ a x * Φ x ∂μ = Φ 0 := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hKcov A _ χ hχc hχmul hχadd hχ0 hχnorm hχker hχinj μ 𝓕 hμ h𝓕 h𝓕1 Φ hΦc hΦper hsum
  classical
  haveI := hμ
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance

  have hχz : ∀ a, χ a 0 = 1 := by
    intro a
    have hne : χ a 0 ≠ 0 := by
      intro h; have := hχnorm a 0; rw [h, norm_zero] at this; exact zero_ne_one this
    have h2 : χ a 0 * χ a 0 = χ a 0 * 1 := by rw [← hχmul, add_zero, mul_one]
    exact (mul_left_cancel₀ hne h2)
  have hχne : ∀ a x, χ a x ≠ 0 := by
    intro a x h; have := hχnorm a x; rw [h, norm_zero] at this; exact zero_ne_one this
  have hstar : ∀ a x, star (χ a x) = χ (-a) x := by
    intro a x
    have h1 : star (χ a x) * χ a x = 1 := by
      have := Complex.conj_mul' (χ a x)
      rw [hχnorm] at this
      simpa using this
    have h2 : χ (-a) x * χ a x = 1 := by rw [← hχadd, neg_add_cancel, hχ0]
    exact mul_right_cancel₀ (hχne a x) (h1.trans h2.symm)
  have hχper : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := by
    intro a γ hγ x
    rw [hχmul, (hχker γ).mpr hγ a, one_mul]

  have lift : ∀ f : G → ℂ, Continuous f → (∀ γ ∈ Γ, ∀ x, f (γ + x) = f x) →
      ∃ F : C(G ⧸ Γ, ℂ), ∀ x : G, F (QuotientAddGroup.mk x) = f x := by
    intro f hf hper
    have hwd : ∀ x y : G, (QuotientAddGroup.mk x : G ⧸ Γ) = QuotientAddGroup.mk y → f x = f y := by
      intro x y hxy
      have h1 := hper _ (QuotientAddGroup.eq.mp hxy) x
      have e : -x + y + x = y := by abel
      rw [e] at h1
      exact h1.symm
    refine ⟨⟨fun q => Quotient.liftOn' q f (fun x y h => hwd x y (Quotient.sound' h)), ?_⟩, fun x => rfl⟩
    exact (QuotientAddGroup.isQuotientMap_mk Γ).continuous_iff.mpr hf

  haveI : CompactSpace (G ⧸ Γ) := by
    refine ⟨?_⟩
    have himg : (QuotientAddGroup.mk '' K : Set (G ⧸ Γ)) = Set.univ := by
      refine Set.eq_univ_of_forall fun q => ?_
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨γ, hγ, hk⟩ := hKcov x
      refine ⟨γ + x, hk, QuotientAddGroup.eq.mpr ?_⟩
      rw [show -(γ + x) + x = -γ by abel]
      exact neg_mem hγ
    rw [← himg]
    exact hK.image QuotientAddGroup.continuous_mk
  have hc : ∀ a, ∃ F : C(G ⧸ Γ, ℂ), ∀ x : G, F (QuotientAddGroup.mk x) = χ a x :=
    fun a => lift _ (hχc a) (hχper a)
  choose e he using hc
  obtain ⟨P, hP⟩ := lift Φ hΦc hΦper

  have h𝓕lt : μ 𝓕 < ⊤ := by rw [h𝓕1]; exact ENNReal.one_lt_top
  have hint : ∀ w : C(G ⧸ Γ, ℂ), IntegrableOn (fun x => w (QuotientAddGroup.mk x)) 𝓕 μ := by
    intro w
    exact Measure.integrableOn_of_bounded h𝓕lt.ne
      (w.continuous.comp QuotientAddGroup.continuous_mk).aestronglyMeasurable
      (M := ‖w‖) (Filter.Eventually.of_forall fun x => w.norm_coe_le_norm _)
  obtain ⟨I, hI⟩ : ∃ I : C(G ⧸ Γ, ℂ) →L[ℂ] ℂ,
      ∀ w, I w = ∫ x in 𝓕, w (QuotientAddGroup.mk x) ∂μ := by
    refine ⟨LinearMap.mkContinuous
      { toFun := fun w => ∫ x in 𝓕, w (QuotientAddGroup.mk x) ∂μ
        map_add' := fun v w => by
          simp only [ContinuousMap.add_apply]
          exact integral_add (hint v) (hint w)
        map_smul' := fun c w => by
          simp only [ContinuousMap.smul_apply, RingHom.id_apply]
          exact integral_smul c _ } 1 (fun w => ?_), fun w => rfl⟩
    calc ‖∫ x in 𝓕, w (QuotientAddGroup.mk x) ∂μ‖ ≤ ‖w‖ * μ.real 𝓕 :=
          norm_setIntegral_le_of_norm_le_const h𝓕lt (fun x _ => w.norm_coe_le_norm _)
      _ = 1 * ‖w‖ := by simp [Measure.real, h𝓕1]

  have hprod : ∀ a a', e a * e a' = e (a + a') := by
    intro a a'; ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp [he, hχadd]
  have hstarE : ∀ a, star (e a) = e (-a) := by
    intro a; ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp only [ContinuousMap.star_apply, he]
    exact hstar a x
  have hone : e 0 = 1 := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp [he, hχ0]
  have hnorm1 : ∀ a, ‖e a‖ ≤ 1 := by
    intro a
    refine (ContinuousMap.norm_le _ zero_le_one).mpr fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [he, hχnorm]

  have hortho : ∀ a, I (e a) = if a = 0 then 1 else 0 := by
    intro a
    rw [hI]
    simp_rw [he]
    split_ifs with ha
    · subst ha
      simp [hχ0, Measure.real, h𝓕1]
    · obtain ⟨y, hy⟩ : ∃ y, χ a y ≠ 1 := by
        by_contra hcon
        push_neg at hcon
        exact ha (hχinj a hcon)
      have htr : IsAddFundamentalDomain Γ (y +ᵥ 𝓕) μ := h𝓕.vadd_of_comm y
      have key : (∫ x in 𝓕, χ a x ∂μ) = χ a y * ∫ x in 𝓕, χ a x ∂μ := by
        calc (∫ x in 𝓕, χ a x ∂μ) = ∫ x in y +ᵥ 𝓕, χ a x ∂μ :=
              h𝓕.setIntegral_eq htr (fun γ x => hχper a γ γ.2 x)
          _ = ∫ x in 𝓕, χ a (y + x) ∂μ := by
              rw [← Set.image_vadd]
              exact (measurePreserving_add_left μ y).setIntegral_image_emb
                (measurableEmbedding_addLeft y) _ _
          _ = ∫ x in 𝓕, χ a y * χ a x ∂μ := by simp_rw [hχmul]
          _ = χ a y * ∫ x in 𝓕, χ a x ∂μ := integral_const_mul _ _
      have h1 : (1 - χ a y) * ∫ x in 𝓕, χ a x ∂μ = 0 := by
        rw [sub_mul, one_mul]
        exact sub_eq_zero.mpr key
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd (sub_eq_zero.mp h).symm hy
      · exact h

  set c : A → ℂ := fun b => ∫ x in 𝓕, χ b x * Φ x ∂μ with hcdef
  have hcoef : ∀ b, c b = I (e b * P) := by
    intro b
    rw [hI]
    simp [hcdef, he, hP]
  have hsumn : Summable (fun a => ‖c a‖) := summable_norm_iff.mpr hsum
  have hgs : Summable (fun a => c a • e (-a)) := by
    refine Summable.of_norm_bounded hsumn fun a => ?_
    calc ‖c a • e (-a)‖ ≤ ‖c a‖ * ‖e (-a)‖ := norm_smul_le _ _
      _ ≤ ‖c a‖ * 1 := by gcongr; exact hnorm1 _
      _ = ‖c a‖ := mul_one _
  set g : C(G ⧸ Γ, ℂ) := ∑' a, c a • e (-a) with hgdef
  have hgcoef : ∀ b, I (e b * g) = c b := by
    intro b
    have step : I (e b * g) = ∑' a, (I.comp (ContinuousLinearMap.mul ℂ C(G ⧸ Γ, ℂ) (e b))) (c a • e (-a)) :=
      (I.comp (ContinuousLinearMap.mul ℂ C(G ⧸ Γ, ℂ) (e b))).map_tsum hgs
    rw [step]
    have hterm : ∀ a, (I.comp (ContinuousLinearMap.mul ℂ C(G ⧸ Γ, ℂ) (e b))) (c a • e (-a)) =
        if a = b then c b else 0 := by
      intro a
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply', mul_smul_comm, map_smul,
        hprod, hortho, smul_eq_mul]
      by_cases h : a = b
      · subst h; simp
      · have h' : b + -a ≠ 0 := fun h' => h (add_neg_eq_zero.mp h').symm
        simp [h, h']
    rw [tsum_congr hterm, tsum_ite_eq]
  set H : C(G ⧸ Γ, ℂ) := P - g with hHdef
  have hH : ∀ b, I (e b * H) = 0 := by
    intro b
    rw [hHdef, mul_sub, map_sub, ← hcoef, hgcoef, sub_self]

  let V : Submodule ℂ C(G ⧸ Γ, ℂ) := Submodule.span ℂ (Set.range e)
  have hVmul : ∀ u ∈ V, ∀ v ∈ V, u * v ∈ V := by
    intro u hu v hv
    have h1 := Submodule.mul_mem_mul hu hv
    rw [Submodule.span_mul_span] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨a', rfl⟩, rfl⟩
    exact ⟨a + a', (hprod a a').symm⟩
  have hVone : (1 : C(G ⧸ Γ, ℂ)) ∈ V := by
    rw [← hone]; exact Submodule.subset_span ⟨0, rfl⟩
  have hVstar : ∀ u ∈ V, star u ∈ V := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [hstarE]
      exact Submodule.subset_span ⟨-a, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [star_add]; exact V.add_mem hx hy
    | smul r x _ hx => rw [star_smul]; exact V.smul_mem _ hx
  let S : StarSubalgebra ℂ C(G ⧸ Γ, ℂ) :=
    { carrier := (V : Set C(G ⧸ Γ, ℂ))
      add_mem' := fun ha hb => V.add_mem ha hb
      zero_mem' := V.zero_mem
      mul_mem' := fun ha hb => hVmul _ ha _ hb
      one_mem' := hVone
      algebraMap_mem' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact V.smul_mem r hVone
      star_mem' := fun ha => hVstar _ ha }
  have hsep : S.SeparatesPoints := by
    intro q q' hne
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q'
    have hnot : -x + y ∉ Γ := fun h => hne (QuotientAddGroup.eq.mpr h)
    obtain ⟨a, ha⟩ : ∃ a, χ a (-x + y) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hnot ((hχker _).mp hcon)
    refine ⟨e a, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ?_⟩
    simp only [he]
    intro heq
    apply ha
    rw [hχmul, ← heq, ← hχmul, neg_add_cancel, hχz]
  have hcl := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep

  have hZ : IsClosed {q : C(G ⧸ Γ, ℂ) | I (q * H) = 0} :=
    isClosed_eq (I.continuous.comp (continuous_id.mul continuous_const)) continuous_const
  have hSZ : (S : Set C(G ⧸ Γ, ℂ)) ⊆ {q : C(G ⧸ Γ, ℂ) | I (q * H) = 0} := by
    intro u hu
    change u ∈ V at hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact hH a
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      rw [add_mul, map_add, hx, hy, add_zero]
    | smul r x _ hx =>
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [smul_mul_assoc, map_smul, hx, smul_zero]
  have hmem : star H ∈ closure (S : Set C(G ⧸ Γ, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, hcl]
    simp
  have hHH : I (star H * H) = 0 := closure_minimal hSZ hZ hmem

  set k : G → ℂ := fun x => H (QuotientAddGroup.mk x) with hkdef
  have hkc : Continuous k := H.continuous.comp QuotientAddGroup.continuous_mk
  have hkper : ∀ γ : Γ, ∀ x, k (γ +ᵥ x) = k x := by
    intro γ x
    show H (QuotientAddGroup.mk ((γ : G) + x)) = H (QuotientAddGroup.mk x)
    congr 1
    refine QuotientAddGroup.eq.mpr ?_
    rw [show -((γ : G) + x) + x = -(γ : G) by abel]
    exact neg_mem γ.2
  have hpt : ∀ x, (star H * H) (QuotientAddGroup.mk x) = ((‖k x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [ContinuousMap.mul_apply, ContinuousMap.star_apply, Complex.ofReal_pow]
    exact Complex.conj_mul' _
  have hr : ∫ x in 𝓕, ‖k x‖ ^ 2 ∂μ = 0 := by
    rw [hI] at hHH
    simp_rw [hpt] at hHH
    rw [integral_complex_ofReal] at hHH
    exact_mod_cast hHH
  have hkint : Integrable (fun x => ‖k x‖ ^ 2) (μ.restrict 𝓕) := by
    refine (hint (star H * H)).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hpt, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hkint).mp hr
  set t : Set G := {x | k x ≠ 0} with htdef
  have ht : IsOpen t := isOpen_ne_fun hkc continuous_const
  have h1 : μ.restrict 𝓕 t = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at hae
    refine measure_mono_null ?_ hae
    intro x hx
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  rw [Measure.restrict_apply ht.measurableSet] at h1
  have h2 : μ t = 0 := by
    refine h𝓕.measure_zero_of_invariant t (fun γ => ?_) h1
    ext x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [htdef, Set.mem_setOf_eq, hkper]
  have h3 : t = ∅ := (ht.measure_eq_zero_iff μ).mp h2
  have hk0 : k 0 = 0 := by
    by_contra hne
    have : (0 : G) ∈ t := hne
    rw [h3] at this
    exact this
  have hg0 : g (QuotientAddGroup.mk 0) = ∑' a, c a := by
    have hev := (ContinuousMap.evalCLM ℂ (QuotientAddGroup.mk 0 : G ⧸ Γ)).map_tsum hgs
    simp only [ContinuousMap.evalCLM_apply] at hev
    rw [hgdef, hev]
    congr 1; funext a
    rw [ContinuousMap.smul_apply, he, hχz, smul_eq_mul, mul_one]
  have : k 0 = Φ 0 - ∑' a, c a := by
    rw [hkdef]
    simp only [hHdef, ContinuousMap.sub_apply, hP]
    rw [hg0]
  rw [hk0] at this
  exact (sub_eq_zero.mp this.symm).symm

end GlobalTheory.SeparatingCharacters
