import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.KapIntegral

noncomputable section

namespace PI.VolStabS

open MeasureTheory Filter Finset PI.VolStabS.RPA
open scoped NNReal ENNReal

theorem rpAbs_holds : RPAbs := by
  intro ι _ W _ m _ L hL hLfin hTail
  classical
  refine ⟨Measure.sum fun S : Finset ι => kap m L S, inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.sum_apply_eq_zero]
    intro S
    refine measure_mono_null ?_ (ae_iff.1 (kap_ae hL S))
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    intro h
    apply hx
    refine Filter.eventually_cofinite.2 ((S.finite_toSet).subset ?_)
    intro i hi
    by_contra hiS
    exact hi ((h i).2 hiS)
  · intro i C hC hCm
    rw [Measure.sum_apply_eq_zero]
    intro S
    apply kap_eval_null hC.compl
    simp only [mu]
    split_ifs
    · exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hCm.le)
    · exact nonpos_iff_eq_zero.1 ((Measure.restrict_apply_le _ _).trans hCm.le)
  · intro f hfi hf
    obtain ⟨T0, hT0⟩ : ∃ T0 : Finset ι, ∀ i ∉ T0, f i = (L i).indicator 1 :=
      ⟨(Filter.eventually_cofinite.1 hf).toFinset, fun i hi => by simpa using hi⟩
    have hsub : ∀ (S : Finset ι) (x : (i : ι) → W i), (∀ i, i ∉ S → x i ∈ L i) →
        Function.mulSupport (fun i => f i (x i)) ⊆ ↑(S ∪ T0) := by
      intro S x hx i hi
      by_contra hni
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, not_or] at hni
      apply hi
      show f i (x i) = 1
      rw [hT0 i hni.2]
      simp [hx i hni.1]
    have hA : ∀ S : Finset ι, (fun x : (i : ι) → W i => ∏ᶠ i, f i (x i)) =ᵐ[kap m L S]
        fun x => ∏ i ∈ S ∪ T0, f i (x i) := by
      intro S
      filter_upwards [kap_ae hL S] with x hx
      exact finprod_eq_prod_of_mulSupport_subset _ (hsub S x fun i hi => (hx i).2 hi)
    have hZ : ∀ S : Finset ι, ¬ S ⊆ T0 →
        (fun x : (i : ι) → W i => ∏ᶠ i, f i (x i)) =ᵐ[kap m L S] 0 := by
      intro S hS
      obtain ⟨j, hjS, hjT⟩ := Finset.not_subset.1 hS
      filter_upwards [kap_ae hL S] with x hx
      refine finprod_eq_zero (fun i => f i (x i)) j ?_
        ((S ∪ T0).finite_toSet.subset (hsub S x fun i hi => (hx i).2 hi))
      rw [hT0 j hjT]
      simp [(hx j).1 hjS]
    have hint : ∀ S : Finset ι, Integrable (fun x : (i : ι) → W i => ∏ᶠ i, f i (x i)) (kap m L S) :=
      fun S => (kap_integral hLfin hTail Finset.subset_union_left f hfi).1.congr (hA S).symm
    have hI : ∀ S : Finset ι, ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S =
        if S ⊆ T0 then (∏ i ∈ T0, ∫ w, f i w ∂mu m L S i) * ((tl m L T0 : ℝ) : ℂ) else 0 := by
      intro S
      split_ifs with h
      · rw [integral_congr_ae (hA S), Finset.union_eq_right.2 h]
        exact (kap_integral hLfin hTail h f hfi).2
      · rw [integral_congr_ae (hZ S h)]
        simp
    have hρint : Integrable (fun x : (i : ι) → W i => ∏ᶠ i, f i (x i))
        (Measure.sum fun S => kap m L S) := by
      refine integrable_sum_measure hint (summable_of_ne_finset_zero (s := T0.powerset) ?_)
      intro S hS
      rw [Finset.mem_powerset] at hS
      have h0 : (fun x : (i : ι) → W i => ‖∏ᶠ i, f i (x i)‖) =ᵐ[kap m L S] fun _ => (0 : ℝ) :=
        (hZ S hS).mono fun x hx => by simp only [Pi.zero_apply] at hx; simp [hx]
      rw [integral_congr_ae h0, integral_zero]
    have hsum : HasSum (fun S : Finset ι => ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S)
        (∑ S ∈ T0.powerset, (∏ i ∈ T0, ∫ w, f i w ∂mu m L S i) * ((tl m L T0 : ℝ) : ℂ)) := by
      have h : HasSum (fun S : Finset ι => ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S)
          (∑ S ∈ T0.powerset, ∫ x, ∏ᶠ i, f i (x i) ∂kap m L S) :=
        hasSum_sum_of_ne_finset_zero (fun S hS => by rw [hI S, if_neg (by simpa using hS)])
      convert h using 1
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [hI S, if_pos (Finset.mem_powerset.1 hS)]
    have hval : ∫ x, ∏ᶠ i, f i (x i) ∂(Measure.sum fun S => kap m L S) =
        (∏ i ∈ T0, ∫ w, f i w ∂m i) * ((tl m L T0 : ℝ) : ℂ) := by
      rw [(hasSum_integral_measure hρint).unique hsum, ← Finset.sum_mul]
      congr 1
      rw [show (∏ i ∈ T0, ∫ w, f i w ∂m i) =
          ∏ i ∈ T0, ((∫ w in (L i)ᶜ, f i w ∂m i) + ∫ w in L i, f i w ∂m i) from
        Finset.prod_congr rfl fun i _ => by rw [add_comm, integral_add_compl (hL i) (hfi i)],
        Finset.prod_add]
      refine Finset.sum_congr rfl fun S hS => ?_
      rw [Finset.mem_powerset] at hS
      rw [← Finset.prod_sdiff hS, mul_comm]
      congr 1
      · exact Finset.prod_congr rfl fun i hi => by simp [mu, hi]
      · exact Finset.prod_congr rfl fun i hi => by simp [mu, (Finset.mem_sdiff.1 hi).2]
    refine ⟨hρint, ?_⟩
    rw [hval]
    have h1 : HasProd (fun i => if i ∈ T0 then ∫ w, f i w ∂m i else 1)
        (∏ i ∈ T0, ∫ w, f i w ∂m i) := by
      convert hasProd_prod_of_ne_finset_one (s := T0)
        (f := fun i => if i ∈ T0 then ∫ w, f i w ∂m i else 1) (fun i hi => if_neg hi) using 1
      all_goals first | infer_instance | exact Finset.prod_congr rfl fun i hi => (if_pos hi).symm
    have h2 : HasProd (fun i => (((({i | i ∉ T0} : Set ι).mulIndicator (am m L) i : ℝ≥0) : ℝ) : ℂ))
        ((tl m L T0 : ℝ) : ℂ) :=
      (hasProd_ind hTail T0).map ((Complex.ofRealHom.toMonoidHom).comp NNReal.toRealHom.toMonoidHom)
        (Complex.continuous_ofReal.comp NNReal.continuous_coe)
    convert h1.mul h2 using 1
    funext i
    by_cases hi : i ∈ T0
    · simp [hi, Set.mulIndicator_apply]
    · have hind : ∫ w, (L i).indicator (1 : W i → ℂ) w ∂m i = (((m i) (L i)).toReal : ℂ) := by
        rw [show (1 : W i → ℂ) = fun _ => (1 : ℂ) from rfl, integral_indicator_const _ (hL i)]
        simp [Measure.real]
      rw [hT0 i hi, hind]
      simp only [hi, if_false, one_mul, Set.mulIndicator_apply, Set.mem_setOf_eq, not_false_eq_true,
        if_true, am, ENNReal.coe_toNNReal_eq_toReal]

end PI.VolStabS
