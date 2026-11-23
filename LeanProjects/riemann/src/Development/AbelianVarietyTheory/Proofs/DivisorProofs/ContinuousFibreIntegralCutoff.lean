import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppendVMemFamAtlasTarget
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePullbackFormLocalCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqEuclideanIntegralOfSupportInChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIsFormPullbackHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMulStatement

set_option autoImplicit false

open Set MeasureTheory Filter
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.CxForm GlobalTheory.BcUnique
open scoped ContDiff Real Topology

namespace GlobalTheory.BcUnique

theorem dens_mul_pull {n m : ℕ} (L : V n →L[ℂ] V m) (c : ℂ) (a : Alt m) :
    dens (algebraMap ℂ (Alt n) c * pull L a) = c * ∑ S, (bas m).repr a S * dens (pull L (bas m S)) := by
  conv_lhs => rw [← (bas m).sum_repr a]
  rw [← Algebra.smul_def]
  simp only [dens, map_sum, map_smul, Finsupp.smul_apply, Finsupp.finsetSum_apply, smul_eq_mul, Finset.sum_div,
    mul_div_assoc]

theorem continuous_integral_fib : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (A : HolAtlas M 1) (α : (famAtlas A).Fld), (famAtlas A).IsForm α → ∀ (χ : M → ℝ) (j : A.ι), A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e j).source → Continuous fun t : OnePoint ℂ => A.integral (A.fn χ * (famAtlas A).pullback A (fib t) α) := by
  intro M _ _ _ _ _ _ A α hα χ j hχ hs
  have hK : IsCompact (tsupport χ) := (isClosed_tsupport χ).isCompact
  set h : OnePoint ℂ → V 1 → ℝ := fun t v =>
    (dens (A.loc (A.fn χ * (famAtlas A).pullback A (fib t) α) j v)).re with hh
  have h0 : ∀ t, ∀ x : A.Pt, x.pt ∉ tsupport χ → (A.fn χ * (famAtlas A).pullback A (fib t) α) x = 0 := by
    intro t x hx
    rw [Pi.mul_apply, HolAtlas.fn, image_eq_zero_of_notMem_tsupport hx]
    simp
  have e : (fun t : OnePoint ℂ => A.integral (A.fn χ * (famAtlas A).pullback A (fib t) α)) =
      fun t => ∫ v, h t v := by
    funext t
    exact A.integral_eq_integral_chart_of_support _ j _ (GlobalTheory.T.isForm_mul_of_isForm_of_isForm A _ _ (A.isForm_fn hχ)
      (GlobalTheory.PullbackForm.isForm_pullback _ _ _ _ _ _ _ _ (isHolo_fib A t) hα)) hK hs (h0 t)
  rw [e]
  have hBc : IsCompact (A.e j '' tsupport χ) := hK.image_of_continuousOn ((A.e j).continuousOn.mono hs)
  have hBt : A.e j '' tsupport χ ⊆ (A.e j).target := by
    rintro _ ⟨y, hy, rfl⟩
    exact (A.e j).map_source (hs hy)
  have hH0 : ∀ t, ∀ v ∉ A.e j '' tsupport χ, h t v = 0 := by
    intro t v hv
    by_cases ht : v ∈ (A.e j).target
    · have hnK : (A.e j).symm v ∉ tsupport χ := fun hk => hv ⟨_, hk, (A.e j).right_inv ht⟩
      simp only [hh, HolAtlas.loc, dif_pos ht]
      erw [h0 t ⟨(j, (A.e j).symm v), (A.e j).map_target ht⟩ hnK]
      simp [dens]
    · simp [hh, HolAtlas.loc, ht, dens]
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  obtain ⟨k, hk⟩ := sphere.cover t₀
  refine ContinuousOn.continuousAt (s := (sphere.e k).source) ?_ ((sphere.e k).open_source.mem_nhds hk)
  refine continuousOn_integral_of_compact_support hBc ?_ fun t v _ hv => hH0 t v hv
  have hform : ∀ p ∈ (sphere.e k).source ×ˢ (A.e j).target, Function.uncurry h p =
      ((χ ((A.e j).symm p.2) : ℂ) * ∑ S, (bas (1 + 1)).repr ((famAtlas A).loc α (j, k)
        (appendV 1 1 (p.2, sphere.e k p.1))) S * dens (pull headIn (bas (1 + 1) S))).re := by
    rintro ⟨t, v⟩ ⟨ht, hv⟩
    rw [← dens_mul_pull, ← GlobalTheory.T.fibre_pullback_form_local_coordinates M A α hα j k t ht v]
    simp only [Function.uncurry, hh, HolAtlas.loc, dif_pos hv]
    rfl
  have hcon : ContinuousOn (Function.uncurry h) ((sphere.e k).source ×ˢ (A.e j).target) := by
    refine ContinuousOn.congr ?_ hform
    refine Complex.continuous_re.comp_continuousOn (ContinuousOn.mul ?_
      (continuousOn_finset_sum _ fun S _ => ContinuousOn.mul ?_ continuousOn_const))
    · exact (hχ j).continuousOn.comp continuousOn_snd fun p hp => ⟨hp.2, trivial⟩
    · refine (hα.smooth (j, k) S).continuousOn.comp
        (f := fun p : OnePoint ℂ × V 1 => appendV 1 1 (p.2, sphere.e k p.1)) ?_ fun p hp => ?_
      · exact (appendV 1 1).continuous.comp_continuousOn (continuousOn_snd.prodMk
          ((sphere.e k).continuousOn.comp continuousOn_fst fun p hp => hp.1))
      · exact (appendV_mem_famAtlas_target A j k _ _).2 ⟨hp.2, (sphere.e k).map_source hp.1⟩
  rintro ⟨t, v⟩ ⟨ht, -⟩
  refine ContinuousAt.continuousWithinAt ?_
  by_cases hv : v ∈ (A.e j).target
  · exact hcon.continuousAt (((sphere.e k).open_source.prod (A.e j).open_target).mem_nhds ⟨ht, hv⟩)
  · have : Function.uncurry h =ᶠ[𝓝 (t, v)] fun _ => 0 := by
      filter_upwards [(hBc.isClosed.isOpen_compl.preimage continuous_snd).mem_nhds
        (show (t, v) ∈ _ from fun h' => hv (hBt h'))] with w hw
      exact hH0 w.1 w.2 hw
    exact continuousAt_const.congr this.symm

end GlobalTheory.BcUnique
