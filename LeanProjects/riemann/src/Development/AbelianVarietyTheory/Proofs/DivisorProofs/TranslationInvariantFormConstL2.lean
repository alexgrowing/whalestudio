import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantSchwartzUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCompactSupportDenseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzPairingContinuousFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealCompactPartitionUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationIsometrySchwartzOperatorStatement

open MeasureTheory Filter Topology
open scoped SchwartzMap

noncomputable section

namespace GlobalTheory.TransConstForm

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def conjS (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) where
  toFun x := starRingEnd ℂ (f x)
  smooth' := Complex.conjCLE.contDiff.comp f.smooth'
  decay' k n := by
    obtain ⟨C, hC⟩ := f.decay' k n
    refine ⟨C, fun x => ?_⟩
    have e : (fun x => starRingEnd ℂ (f x)) = (Complex.conjLIE : ℂ ≃ₗᵢ[ℝ] ℂ) ∘ f := by
      funext y; simp
    rw [e, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem conjS_apply (f : 𝓢(V, ℂ)) (x : V) : conjS f x = starRingEnd ℂ (f x) := rfl

def mulS (m f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) := SchwartzMap.smulLeftCLM ℂ (m : V → ℂ) f

theorem mulS_apply (m f : 𝓢(V, ℂ)) (x : V) : mulS m f x = m x * f x := by
  have := congrFun (SchwartzMap.smulLeftCLM_apply (F := ℂ) m.hasTemperateGrowth f) x
  simpa [mulS, smul_eq_mul] using this

def evS (x : V) : 𝓢(V, ℂ) →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ V ℂ)

theorem evS_apply (x : V) (f : 𝓢(V, ℂ)) : evS x f = f x := rfl

theorem sum_apply {ι : Type} (s : Finset ι) (F : ι → 𝓢(V, ℂ)) (x : V) : (∑ i ∈ s, F i) x = ∑ i ∈ s, F i x := by
  rw [← evS_apply x, map_sum]; rfl

theorem trans_apply (a : V) (f : 𝓢(V, ℂ)) (x : V) : SchwartzMap.compSubConstCLM ℂ a f x = f (x - a) := by
  simp

theorem exists_bump [FiniteDimensional ℝ V] (K : Set V) (hK : IsCompact K) :
    ∃ χ : 𝓢(V, ℂ), HasCompactSupport (χ : V → ℂ) ∧ (∀ x, starRingEnd ℂ (χ x) = χ x) ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have h0 : (0 : ℝ) < max R 1 := lt_max_of_lt_right one_pos
  let b : ContDiffBump (0 : V) := ⟨max R 1, max R 1 + 1, h0, by linarith⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), h1, fun x => ?_, fun x hx => ?_⟩
  · change starRingEnd ℂ ((b x : ℝ) : ℂ) = ((b x : ℝ) : ℂ)
    simp
  · change ((b x : ℝ) : ℂ) = 1
    rw [b.one_of_mem_closedBall]
    · simp
    · exact Metric.closedBall_subset_closedBall (le_max_left _ _) (hR hx)

end GlobalTheory.TransConstForm

namespace GlobalTheory.TransConstForm

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem exists_lambda [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ))
    (htr : ∀ (a : V) (f f' g g' : 𝓢(V, ℂ)), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      ∫ x, T f' x * starRingEnd ℂ (T g' x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ)
    (hmul : ∀ (m f f' g g' : 𝓢(V, ℂ)), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      ∫ x, T f' x * starRingEnd ℂ (T g x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ) :
    ∃ Λ : 𝓢(V, ℂ) →L[ℂ] ℂ, ∀ f g h : 𝓢(V, ℂ), HasCompactSupport (f : V → ℂ) →
      (∀ x, h x = f x * starRingEnd ℂ (g x)) → ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = Λ h := by
  classical
  set B : 𝓢(V, ℂ) → 𝓢(V, ℂ) → ℂ := fun f g => ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ with hB
  have hL : ∀ g, ∃ L : 𝓢(V, ℂ) →L[ℂ] ℂ, ∀ f, L f = B f g := fun g => by
    obtain ⟨L, hL⟩ := GlobalTheory.T.schwartz_pairing_continuous_functional V μ (T g)
    exact ⟨L.comp T, fun f => by simp [hL, hB]⟩
  choose L hLB using hL
  obtain ⟨ψ, hψc, hψr, v, hsum1, hfin, M, hsumm⟩ := GlobalTheory.T.real_compact_partition_unity V
  obtain ⟨χ, hχc, hχr, hχ1⟩ := exists_bump (tsupport (ψ : V → ℂ)) hψc
  let tr : V → 𝓢(V, ℂ) → 𝓢(V, ℂ) := fun a f => SchwartzMap.compSubConstCLM ℂ a f
  have htr_apply : ∀ a f x, tr a f x = f (x - a) := fun a f x => trans_apply a f x
  have hχψ : ∀ y, starRingEnd ℂ (χ y) * ψ y = ψ y := by
    intro y
    by_cases hy : ψ y = 0
    · simp [hy]
    · rw [hχr, hχ1 y (subset_tsupport _ hy), one_mul]
  have hterm : ∀ h, ∃ C : ℝ, ∀ j, ‖B h (tr (v j) ψ)‖ ≤ C * ((1 + ‖v j‖) ^ M)⁻¹ := by
    intro h
    obtain ⟨C, hC⟩ := GlobalTheory.T.translation_isometry_schwartz_operator V μ T htr χ ψ h hχc M
    refine ⟨C, fun j => ?_⟩
    have e : B h (tr (v j) ψ) = B (mulS (tr (v j) χ) h) (tr (v j) ψ) :=
      (hmul (tr (v j) χ) h (mulS (tr (v j) χ) h) (tr (v j) ψ) (tr (v j) ψ)
        (fun x => mulS_apply _ _ x) (fun x => by simp only [htr_apply]; exact (hχψ _).symm)).symm
    rw [e]
    exact hC (v j) _ _ (fun x => by rw [mulS_apply, htr_apply]) (fun x => htr_apply _ _ x)
  have hsummable : ∀ h, Summable (fun j => L (tr (v j) ψ) h) := by
    intro h
    obtain ⟨C, hC⟩ := hterm h
    refine Summable.of_norm_bounded (hsumm.mul_left C) (fun j => ?_)
    rw [hLB]; exact hC j
  haveI : BarrelledSpace ℂ 𝓢(V, ℂ) := GlobalTheory.schwartzMap_barrelledSpace V
  obtain ⟨en, hen⟩ := exists_surjective_nat (Fin (Module.finrank ℝ V) → ℤ)
  let S : ℕ → Finset (Fin (Module.finrank ℝ V) → ℤ) := fun N => (Finset.range N).image en
  have hS : Tendsto S atTop atTop := by
    refine Filter.tendsto_atTop_finset_of_monotone (fun a b hab => ?_) (fun w => ?_)
    · exact Finset.image_subset_image (Finset.range_subset_range.2 hab)
    · obtain ⟨k, rfl⟩ := hen w
      exact ⟨k + 1, Finset.mem_image_of_mem _ (Finset.mem_range.2 (Nat.lt_succ_self k))⟩
  have hlim : Tendsto (fun N h => (∑ j ∈ S N, L (tr (v j) ψ)) h) atTop
      (𝓝 fun h : 𝓢(V, ℂ) => ∑' j, L (tr (v j) ψ) h) := by
    rw [tendsto_pi_nhds]
    intro h
    simp only [ContinuousLinearMap.sum_apply]
    exact (hsummable h).hasSum.comp hS
  refine ⟨continuousLinearMapOfTendsto (fun N => ∑ j ∈ S N, L (tr (v j) ψ)) hlim, fun f g h hf hh => ?_⟩
  show _ = linearMapOfTendsto _ _ hlim h
  rw [linearMapOfTendsto_apply]
  obtain ⟨R, hR⟩ := hf.isCompact.isBounded.subset_closedBall 0
  obtain ⟨r, hr⟩ := hψc.isCompact.isBounded.subset_closedBall 0
  set J := (hfin (R + r)).toFinset with hJ
  have hout : ∀ j, j ∉ J → ∀ x, ψ (x - v j) * f x = 0 := by
    intro j hj x
    by_contra hne
    have h1 : ψ (x - v j) ≠ 0 := left_ne_zero_of_mul hne
    have h2 : f x ≠ 0 := right_ne_zero_of_mul hne
    have hx : ‖x‖ ≤ R := by simpa using hR (subset_tsupport _ h2)
    have hy : ‖x - v j‖ ≤ r := by simpa using hr (subset_tsupport _ h1)
    apply hj
    rw [hJ, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    calc ‖v j‖ = ‖x - (x - v j)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖x‖ + ‖x - v j‖ := norm_sub_le _ _
      _ ≤ R + r := add_le_add hx hy
  have hterm_eq : ∀ j, L (tr (v j) ψ) h = B (mulS (tr (v j) ψ) f) g := by
    intro j
    rw [hLB]
    have ea := hmul (conjS g) f h (tr (v j) ψ) (mulS (tr (v j) ψ) g)
      (fun x => by rw [hh, conjS_apply, mul_comm])
      (fun x => by rw [mulS_apply, conjS_apply, Complex.conj_conj, mul_comm])
    have eb := hmul (tr (v j) ψ) f (mulS (tr (v j) ψ) f) g (mulS (tr (v j) ψ) g)
      (fun x => mulS_apply _ _ x)
      (fun x => by rw [mulS_apply, htr_apply, hψr])
    exact ea.trans eb.symm
  have hzero : ∀ j, j ∉ J → mulS (tr (v j) ψ) f = 0 := by
    intro j hj
    ext x
    rw [mulS_apply, htr_apply]
    exact hout j hj x
  have hsumf : ∑ j ∈ J, mulS (tr (v j) ψ) f = f := by
    ext x
    rw [sum_apply]
    simp only [mulS_apply, htr_apply]
    rw [← Finset.sum_mul]
    by_cases hfx : f x = 0
    · simp [hfx]
    · have hs : HasSum (fun j => ψ (x - v j)) (∑ j ∈ J, ψ (x - v j)) := by
        refine hasSum_sum_of_ne_finset_zero (fun j hj => ?_)
        have := hout j hj x
        exact (mul_eq_zero.1 this).resolve_right hfx
      rw [← (hsum1 x).unique hs, one_mul]
  calc B f g = L g f := (hLB g f).symm
    _ = L g (∑ j ∈ J, mulS (tr (v j) ψ) f) := by rw [hsumf]
    _ = ∑ j ∈ J, B (mulS (tr (v j) ψ) f) g := by rw [map_sum]; simp only [hLB]
    _ = ∑ j ∈ J, L (tr (v j) ψ) h := Finset.sum_congr rfl (fun j _ => (hterm_eq j).symm)
    _ = ∑' j, L (tr (v j) ψ) h := by
      refine (tsum_eq_sum (fun j hj => ?_)).symm
      rw [hterm_eq, hzero j hj, ← hLB, map_zero]

end GlobalTheory.TransConstForm

namespace GlobalTheory.TransConstForm

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem main_of [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, ℂ))
    (htr : ∀ (a : V) (f f' g g' : 𝓢(V, ℂ)), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      ∫ x, T f' x * starRingEnd ℂ (T g' x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ)
    (hmul : ∀ (m f f' g g' : 𝓢(V, ℂ)), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      ∫ x, T f' x * starRingEnd ℂ (T g x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g' x) ∂μ) :
    ∃ c : ℂ, ∀ f g : 𝓢(V, ℂ),
      ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = c * ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  classical
  obtain ⟨Λ, hΛ⟩ := exists_lambda μ T htr hmul
  set B : 𝓢(V, ℂ) → 𝓢(V, ℂ) → ℂ := fun f g => ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ with hB
  have hL : ∀ g, ∃ L : 𝓢(V, ℂ) →L[ℂ] ℂ, ∀ f, L f = B f g := fun g => by
    obtain ⟨L, hL⟩ := GlobalTheory.T.schwartz_pairing_continuous_functional V μ (T g)
    exact ⟨L.comp T, fun f => by simp [hL, hB]⟩
  choose L hLB using hL
  let tr : V → 𝓢(V, ℂ) → 𝓢(V, ℂ) := fun a f => SchwartzMap.compSubConstCLM ℂ a f
  have htr_apply : ∀ a f x, tr a f x = f (x - a) := fun a f x => trans_apply a f x
  have hΛc : ∀ h : 𝓢(V, ℂ), HasCompactSupport (h : V → ℂ) → ∀ a, Λ (tr a h) = Λ h := by
    intro h hh a
    obtain ⟨χ, hχc, hχr, hχ1⟩ := exists_bump (tsupport (h : V → ℂ)) hh
    have e1 : B h χ = Λ h := hΛ h χ h hh (fun x => by
      by_cases hx : h x = 0
      · simp [hx]
      · rw [hχr, hχ1 x (subset_tsupport _ hx), mul_one])
    have hh' : HasCompactSupport (tr a h : V → ℂ) := by
      have : (tr a h : V → ℂ) = (h : V → ℂ) ∘ (Homeomorph.subRight a) := by
        funext x; simp [htr_apply]
      rw [this]; exact hh.comp_homeomorph _
    have e2 : B (tr a h) (tr a χ) = Λ (tr a h) := hΛ _ _ _ hh' (fun x => by
      rw [htr_apply, htr_apply]
      by_cases hx : h (x - a) = 0
      · simp [hx]
      · rw [hχr, hχ1 _ (subset_tsupport _ hx), mul_one])
    have e3 : B h χ = B (tr a h) (tr a χ) :=
      htr a (tr a h) h (tr a χ) χ (fun x => by rw [htr_apply, add_sub_cancel_right])
        (fun x => by rw [htr_apply, add_sub_cancel_right])
    rw [← e2, ← e1, e3]
  have hΛt : ∀ a h, Λ (tr a h) = Λ h := by
    intro a h
    have hcl : IsClosed {h : 𝓢(V, ℂ) | Λ (tr a h) = Λ h} :=
      isClosed_eq (Λ.continuous.comp (SchwartzMap.compSubConstCLM ℂ a).continuous) Λ.continuous
    exact closure_minimal (fun h hh => hΛc h hh a) hcl (GlobalTheory.T.schwartz_compact_support_dense V h)
  have hΛt' : ∀ (a : V) (f g : 𝓢(V, ℂ)), (⇑g = fun x => f (x + a)) → Λ g = Λ f := by
    intro a f g hg
    have : g = tr (-a) f := by
      ext x; rw [htr_apply, sub_neg_eq_add]; exact congrFun hg x
    rw [this, hΛt]
  let I : 𝓢(V, ℂ) →L[ℂ] ℂ := SchwartzMap.integralCLM ℂ μ
  have hIa : ∀ u, I u = ∫ x, u x ∂μ := fun u => SchwartzMap.integralCLM_apply ℂ u
  have hIt : ∀ (a : V) (f g : 𝓢(V, ℂ)), (⇑g = fun x => f (x + a)) → I g = I f := by
    intro a f g hg
    rw [hIa, hIa, hg]
    exact integral_add_right_eq_self (fun x => f x) a
  have hI0 : I ≠ 0 := by
    intro h0
    let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
    have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
      b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    have := congrArg (fun F : 𝓢(V, ℂ) →L[ℂ] ℂ => F (h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff))) h0
    simp only [ContinuousLinearMap.zero_apply, hIa] at this
    change ∫ x, ((b x : ℝ) : ℂ) ∂μ = 0 at this
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at this
    exact (ne_of_gt (b.integral_pos (μ := μ))) this
  obtain ⟨c, hc⟩ := GlobalTheory.TransInvSchwartz.dim_le_one I Λ hIt hΛt' hI0
  refine ⟨c, fun f g => ?_⟩
  obtain ⟨P, hP⟩ := GlobalTheory.T.schwartz_pairing_continuous_functional V μ g
  have hcl : IsClosed {f : 𝓢(V, ℂ) | B f g = c * ∫ x, f x * starRingEnd ℂ (g x) ∂μ} := by
    have e : {f : 𝓢(V, ℂ) | B f g = c * ∫ x, f x * starRingEnd ℂ (g x) ∂μ} = {f | L g f = c * P f} := by
      ext f; simp only [Set.mem_setOf_eq, hLB, hP]
    rw [e]; exact isClosed_eq (L g).continuous (continuous_const.mul P.continuous)
  refine closure_minimal (fun f hf => ?_) hcl (GlobalTheory.T.schwartz_compact_support_dense V f)
  have := hΛ f g (mulS f (conjS g)) hf (fun x => by rw [mulS_apply, conjS_apply])
  show B f g = _
  rw [show B f g = Λ (mulS f (conjS g)) from this, hc, ContinuousLinearMap.smul_apply, smul_eq_mul, hIa]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [mulS_apply, conjS_apply]

end GlobalTheory.TransConstForm

theorem GlobalTheory.TransConstForm.eq_const_mul_l2_of_translation_invariant : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @MeasureTheory.Measure V (borel V)), @MeasureTheory.Measure.IsAddHaarMeasure V _ _ (borel V) μ →
    ∀ (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (a : V) (f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g' x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x))) →
    (∀ (m f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = m x * f x) → (∀ x, g' x = starRingEnd ℂ (m x) * g x) →
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f' x * starRingEnd ℂ (T g x)) =
        @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g' x))) →
    ∃ c : ℂ, ∀ f g : SchwartzMap V ℂ,
      @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => T f x * starRingEnd ℂ (T g x)) =
        c * @MeasureTheory.integral V ℂ _ _ (borel V) μ (fun x => f x * starRingEnd ℂ (g x)) := by
  intro V _ _ _ μ hμ T htr hmul
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  exact GlobalTheory.TransConstForm.main_of μ T htr hmul
