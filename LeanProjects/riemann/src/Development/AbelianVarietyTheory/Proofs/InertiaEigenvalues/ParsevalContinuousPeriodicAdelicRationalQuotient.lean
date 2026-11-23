import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodicEqZeroOfFourierCoefficientsZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.AdelicParseval

theorem hasSum_sq_inner_of_mem_closure {H A : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {v : A → H} (hv : Orthonormal ℂ v) {x : H}
    (hx : x ∈ (Submodule.span ℂ (Set.range v)).topologicalClosure) :
    HasSum (fun a => ‖inner ℂ (v a) x‖ ^ 2) (‖x‖ ^ 2) := by
  classical
  have hr := hv.orthogonalFamily.range_linearIsometry
  have hle : Submodule.span ℂ (Set.range v) ≤
      ⨆ i, LinearMap.range (LinearIsometry.toSpanSingleton ℂ H (hv.1 i)).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine Submodule.mem_iSup_of_mem a ⟨1, ?_⟩
    simp
  have hx' := Submodule.topologicalClosure_mono hle hx
  rw [← hr] at hx'
  obtain ⟨c, rfl⟩ := hx'
  have hs := hv.orthogonalFamily.hasSum_linearIsometry c
  have hc : ∀ a, inner ℂ (v a) (hv.orthogonalFamily.linearIsometry c) = c a := by
    intro a
    have h1 := (innerSL ℂ (v a)).hasSum hs
    have h2 : HasSum (fun b => innerSL ℂ (v a) (LinearIsometry.toSpanSingleton ℂ H (hv.1 b) (c b))) (c a) := by
      convert hasSum_ite_eq a (c a) using 2 with b
      simp only [LinearIsometry.toSpanSingleton_apply, innerSL_apply_apply, inner_smul_right,
        orthonormal_iff_ite.1 hv a b]
      by_cases h : a = b
      · subst h; simp
      · simp [h, Ne.symm h]
    exact h1.unique h2
  have hn := lp.hasSum_norm (p := 2) (by simp) c
  simp only [LinearIsometry.coe_toLinearMap, hc, LinearIsometry.norm_map]
  simpa using hn

theorem hasSum_sq_integral {X A : Type} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [DecidableEq A] (m : Measure X) [IsFiniteMeasure m]
    (e : A → C(X, ℂ)) (h1 : ∃ a, e a = 1) (hmul : ∀ a b, ∃ c, e c = e a * e b) (hstar : ∀ a, ∃ c, e c = star (e a))
    (hsep : ∀ x y, x ≠ y → ∃ a, e a x ≠ e a y)
    (horth : ∀ a b, ∫ x, (starRingEnd ℂ) (e a x) * e b x ∂m = if a = b then 1 else 0) (φ : C(X, ℂ)) :
    HasSum (fun a => ‖∫ x, (starRingEnd ℂ) (e a x) * φ x ∂m‖ ^ 2) (∫ x, ‖φ x‖ ^ 2 ∂m) := by
  let T : C(X, ℂ) →L[ℂ] Lp ℂ 2 m := ContinuousMap.toLp 2 m ℂ
  have hT : ∀ p q : C(X, ℂ), inner ℂ (T p) (T q) = ∫ x, (starRingEnd ℂ) (p x) * q x ∂m := by
    intro p q
    rw [ContinuousMap.inner_toLp]
    simp only [mul_comm]
  let V : Submodule ℂ C(X, ℂ) := Submodule.span ℂ (Set.range e)
  have hV1 : (1 : C(X, ℂ)) ∈ V := Submodule.subset_span h1
  have hVmul : ∀ p ∈ V, ∀ q ∈ V, p * q ∈ V := by
    intro p hp q hq
    have : V * V ≤ V := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      exact hmul a b
    exact this (Submodule.mul_mem_mul hp hq)
  have hVstar : ∀ p ∈ V, star p ∈ V := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span (hstar a)
    | zero => rw [star_zero]; exact V.zero_mem
    | add x y _ _ hx hy => rw [star_add]; exact V.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact V.smul_mem _ hx
  let S : StarSubalgebra ℂ C(X, ℂ) :=
    { toSubalgebra := V.toSubalgebra hV1 (fun p q hp hq => hVmul p hp q hq)
      star_mem' := fun {p} hp => hVstar p hp }
  have hS : S.topologicalClosure = ⊤ := by
    refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
    intro x y hxy
    obtain ⟨a, ha⟩ := hsep x y hxy
    exact ⟨e a, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ha⟩
  have hv : Orthonormal ℂ (fun a => T (e a)) := by
    rw [orthonormal_iff_ite]
    intro a b
    rw [hT, horth]
  let W := (Submodule.span ℂ (Set.range fun a => T (e a))).topologicalClosure
  have hcl : IsClosed {p : C(X, ℂ) | T p ∈ W} :=
    (Submodule.isClosed_topologicalClosure _).preimage T.continuous
  have hsub : (S : Set C(X, ℂ)) ⊆ {p : C(X, ℂ) | T p ∈ W} := by
    intro p hp
    have hp' : p ∈ V := hp
    show T p ∈ W
    clear hp
    induction hp' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a, rfl⟩)
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact W.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact W.smul_mem _ hx
  have hφ : φ ∈ S.topologicalClosure := by rw [hS]; trivial
  have h0 : T φ ∈ W := closure_minimal hsub hcl hφ
  have hs := hasSum_sq_inner_of_mem_closure hv h0
  simp only [hT] at hs
  have hn : ‖T φ‖ ^ 2 = ∫ x, ‖φ x‖ ^ 2 ∂m := by
    have h2 := hT φ φ
    rw [inner_self_eq_norm_sq_to_K] at h2
    have h3 : ∫ x, (starRingEnd ℂ) (φ x) * φ x ∂m = ∫ x, ((‖φ x‖ ^ 2 : ℝ) : ℂ) ∂m :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [Complex.conj_mul'])
    rw [h3, integral_complex_ofReal] at h2
    apply Complex.ofReal_injective
    rw [← h2, Complex.ofReal_pow]
    rfl
  rwa [hn] at hs

theorem tsum_enorm_sq_integral {X G A : Type} [TopologicalSpace X] [CompactSpace X] [TopologicalSpace G]
    [MeasurableSpace G] [OpensMeasurableSpace G] [DecidableEq A] (ν : Measure G) [IsFiniteMeasure ν] (π : G → X)
    (hπ : Continuous π)
    (e : A → C(X, ℂ)) (h1 : ∃ a, e a = 1) (hmul : ∀ a b, ∃ c, e c = e a * e b) (hstar : ∀ a, ∃ c, e c = star (e a))
    (hsep : ∀ x y, x ≠ y → ∃ a, e a x ≠ e a y)
    (horth : ∀ a b, ∫ x, (starRingEnd ℂ) (e a (π x)) * e b (π x) ∂ν = if a = b then 1 else 0) (φ : C(X, ℂ)) :
    ∑' a, ‖∫ x, (starRingEnd ℂ) (e a (π x)) * φ (π x) ∂ν‖ₑ ^ 2 = ∫⁻ x, ‖φ (π x)‖ₑ ^ 2 ∂ν := by
  letI : MeasurableSpace X := borel X
  haveI : BorelSpace X := ⟨rfl⟩
  have hm : AEMeasurable π ν := hπ.measurable.aemeasurable
  have hi : ∀ p q : C(X, ℂ), ∫ x, (starRingEnd ℂ) (p x) * q x ∂(ν.map π) =
      ∫ x, (starRingEnd ℂ) (p (π x)) * q (π x) ∂ν := fun p q =>
    integral_map hm ((Complex.continuous_conj.comp p.continuous).mul q.continuous).aestronglyMeasurable
  have hs := hasSum_sq_integral (ν.map π) e h1 hmul hstar hsep (fun a b => by rw [hi, horth]) φ
  simp only [hi] at hs
  rw [integral_map (f := fun x => ‖φ x‖ ^ 2) hm (φ.continuous.norm.pow 2).aestronglyMeasurable] at hs
  have hint : Integrable (fun x => ‖φ (π x)‖ ^ 2) ν :=
    Integrable.of_bound ((φ.continuous.comp hπ).norm.pow 2).aestronglyMeasurable (‖φ‖ ^ 2)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (φ.norm_coe_le_norm _) 2)
  have h2 := ENNReal.ofReal_tsum_of_nonneg (fun a => sq_nonneg _) hs.summable
  rw [hs.tsum_eq, ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)] at h2
  simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm] at h2
  exact h2.symm

variable {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι] {ψ : AddChar (Ad E) ℂ}

theorem conj_psi (hψ : StdPsi ψ) (y : Ad E) : (starRingEnd ℂ) (ψ y) = ψ (-y) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ.norm]
  simp

theorem exists_dot_ne_one (hψ : StdPsi ψ) {ξ : ι → E} (hξ : ξ ≠ 0) : ∃ y : ι → Ad E, ψ (-dot ξ y) ≠ 1 := by
  classical
  obtain ⟨t, ht⟩ := Function.ne_iff.1 hξ
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  obtain ⟨y, hy⟩ := hψ.loc ⟨M, hM.isPrime,
    Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩
  generalize sFin E _ = z at hy
  refine ⟨Pi.single t (-(algebraMap E (Ad E) (ξ t)⁻¹ * z)), ?_⟩
  rw [dot, Finset.sum_eq_single t]
  · rw [Pi.single_eq_same, mul_neg, neg_neg, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
    exact hy
  · intro s _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

theorem avg_char_eq_zero (hψ : StdPsi ψ) {ξ : ι → E} (hξ : ξ ≠ 0) :
    avg (ratV E ι) (fun x => ψ (-dot ξ x) * 1) = 0 := by
  obtain ⟨y, hy⟩ := exists_dot_ne_one hψ hξ
  have hP : Per (ratV E ι) (fun x => ψ (-dot ξ x) * 1) :=
    hψ.per_twist (Φ := fun _ => 1) ⟨continuous_const, fun _ _ _ => rfl⟩ ξ
  have h1 := avg_add_right _ _ (isCoLat_ratV E ι) _ hP y
  have h2 : (fun x => ψ (-dot ξ (x + y)) * 1) = fun x => ψ (-dot ξ y) * (ψ (-dot ξ x) * 1) := by
    funext x
    rw [dot_add_right, neg_add, AddChar.map_add_eq_mul]
    ring
  rw [h2, avg_const_mul] at h1
  have h3 : (ψ (-dot ξ y) - 1) * avg (ratV E ι) (fun x => ψ (-dot ξ x) * 1) = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hy)

theorem dot_neg_left (ξ : ι → E) (x : ι → Ad E) : dot (-ξ) x = -dot ξ x := by
  simp [dot]

theorem tsum_enorm_avg_sq : ∀ (E : Type) [Field E] [NumberField E] (ι : Type) [Fintype ι] (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ Φ : (ι → Ad E) → ℂ, Per (ratV E ι) Φ → ∀ [MeasurableSpace (ι → Ad E)] [BorelSpace (ι → Ad E)] (ν : Measure (ι → Ad E)) (D : Set (ι → Ad E)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratV E ι) D ν → ν D = 1 → ∑' ξ : ι → E, ‖avg (ratV E ι) (fun x => ψ (-dot ξ x) * Φ x)‖ₑ ^ 2 = ∫⁻ x in D, ‖Φ x‖ₑ ^ 2 ∂ν := by
  classical
  intro E _ _ ι _ ψ hψ Φ hΦ _ _ ν D hν hD h1
  have hL := isCoLat_ratV E ι
  obtain ⟨-, K, hK, hcov⟩ := id hL
  set Γ := ratV E ι with hΓ
  have hav : ∀ f, Per Γ f → avg Γ f = ∫ x in D, f x ∂ν := fun f hf => by
    rw [(setIntegral_eq_mass_mul_avg _ Γ hL ν D hν hD f hf).2.2.2, h1]
    simp
  have : IsFiniteMeasure (ν.restrict D) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hπ : Continuous (QuotientAddGroup.mk : (ι → Ad E) → (ι → Ad E) ⧸ Γ) := QuotientAddGroup.continuous_mk
  have : CompactSpace ((ι → Ad E) ⧸ Γ) := ⟨by
    refine (hK.image hπ).of_isClosed_subset isClosed_univ fun q _ => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨γ, hγ, hk⟩ := hcov x
    refine ⟨γ + x, hk, QuotientAddGroup.eq.2 ?_⟩
    simpa using hγ⟩
  have desc : ∀ f : (ι → Ad E) → ℂ, Per Γ f →
      ∃ p : C((ι → Ad E) ⧸ Γ, ℂ), ∀ x : ι → Ad E, p (x : (ι → Ad E) ⧸ Γ) = f x := by
    intro f hf
    have hw : ∀ x y : ι → Ad E, (QuotientAddGroup.leftRel Γ) x y → f x = f y := by
      intro x y hxy
      rw [QuotientAddGroup.leftRel_apply] at hxy
      rw [← hf.2 _ hxy x]
      congr 1
      abel
    exact ⟨⟨Quotient.lift f hw, hf.1.quotient_lift hw⟩, fun x => rfl⟩
  have hP : ∀ ξ : ι → E, Per Γ (fun x => ψ (-dot ξ x) * 1) := fun ξ =>
    hψ.per_twist (Φ := fun _ => 1) ⟨continuous_const, fun _ _ _ => rfl⟩ ξ
  choose e he using fun a : ι → E => desc _ (hP (-a))
  simp only [dot_neg_left, neg_neg, mul_one] at he
  obtain ⟨φ, hφ⟩ := desc Φ hΦ
  have ext : ∀ p q : C((ι → Ad E) ⧸ Γ, ℂ),
      (∀ x : ι → Ad E, p (x : (ι → Ad E) ⧸ Γ) = q (x : (ι → Ad E) ⧸ Γ)) → p = q := by
    intro p q h
    ext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact h x
  have key := tsum_enorm_sq_integral (ν.restrict D) _ hπ e
    ⟨0, ext _ _ fun x => by simp [he, dot_zero_left]⟩
    (fun a b => ⟨a + b, ext _ _ fun x => by simp [he, dot_add_left, AddChar.map_add_eq_mul]⟩)
    (fun a => ⟨-a, ext _ _ fun x => by simp [he, dot_neg_left, conj_psi hψ]⟩)
    (fun z w hzw => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
      obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective w
      by_contra hcon
      push Not at hcon
      refine hzw (QuotientAddGroup.eq.2 ((hψ.forall_dot_eq_one_iff _).1 fun a => ?_))
      have h1 := hcon a
      rw [he, he] at h1
      have hne : ψ (dot a y) ≠ 0 := fun h => by simpa [h] using hψ.norm (dot a y)
      refine mul_left_cancel₀ hne ?_
      rw [mul_one, ← AddChar.map_add_eq_mul, ← h1]
      congr 1
      rw [add_neg_eq_iff_eq_add, ← dot_add_right, add_neg_cancel_left])
    (fun a b => by
      simp only [he, conj_psi hψ]
      have h2 : ∀ x, ψ (-dot a x) * ψ (dot b x) = ψ (-dot (a - b) x) * 1 := fun x => by
        rw [mul_one, ← AddChar.map_add_eq_mul, sub_eq_add_neg, dot_add_left, dot_neg_left, neg_add, neg_neg]
      simp only [h2]
      split_ifs with hab
      · subst hab
        simp [dot_zero_left, Measure.real, h1]
      · rw [← hav _ (hP (a - b))]
        exact avg_char_eq_zero hψ (sub_ne_zero.2 hab))
    φ
  simp only [he, hφ, conj_psi hψ] at key
  rw [← key]
  exact tsum_congr fun ξ => by rw [hav _ (hψ.per_twist hΦ ξ)]

end GlobalTheory.AdelicParseval
