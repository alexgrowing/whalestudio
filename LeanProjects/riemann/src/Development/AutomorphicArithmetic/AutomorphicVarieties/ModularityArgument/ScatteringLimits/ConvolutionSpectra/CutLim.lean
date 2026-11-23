import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.CutLaws

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.cutLim :
    ∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] (u : L V), (∀ T : ℝ, Tendsto (fun t => cut V (Ioi T) (sh V t u)) atTop (𝓝 0)) ∧
      ∀ a d : ℝ, 0 < d → HasSum (fun n : ℤ => cut V (Ioc (a + n * d) (a + (n + 1) * d)) u) u := by
  intro V _ _ _ _ u
  have hi : Integrable fun x => ‖u x‖ ^ 2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).1 (Lp.memLp u)
  have key : ∀ {ι : Type} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated] (s : ι → Set ℝ), (∀ i, MeasurableSet (s i)) →
      Antitone s → ⋂ i, s i = ∅ → [Nonempty ι] → Tendsto (fun i => ‖cut V (s i) u‖) atTop (𝓝 0) := by
    intro ι _ _ s hm ha he _
    have h1 := tendsto_setIntegral_of_antitone (μ := volume) (f := fun x => ‖u x‖ ^ 2) hm ha ⟨Classical.arbitrary ι, hi.integrableOn⟩
    rw [he, setIntegral_empty] at h1
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    refine h2.congr fun i => ?_
    rw [Function.comp_apply, ← (cutLaws (V := V) (s i) (s i) (hm i) (hm i)).2.2.2.2.2.2.2.2 u, Real.sqrt_sq (norm_nonneg _)]
  refine ⟨fun T => ?_, fun a d hd => ?_⟩
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    refine (key (fun t : ℝ => Ioi (T + t)) (fun _ => measurableSet_Ioi) (fun x y h => Ioi_subset_Ioi (by linarith)) ?_).congr fun t => ?_
    · refine eq_empty_of_forall_notMem fun x hx => ?_
      have := mem_iInter.1 hx (x - T)
      simp at this
    · have h := DFunLike.congr_fun ((cutLaws (V := V) (Ioi (T + t)) univ measurableSet_Ioi .univ).2.2.2.2.2.2.1 t) u
      simp only [ContinuousLinearMap.comp_apply, preimage_add_const_Ioi, add_sub_cancel_right] at h
      rw [← h]; exact ((shF V).norm t _).symm
  · set I : ℤ → Set ℝ := fun n => Ioc (a + n * d) (a + (n + 1) * d) with hI
    have hm : ∀ F : Finset ℤ, MeasurableSet (⋃ n ∈ F, I n) := fun F => F.measurableSet_biUnion fun _ _ => measurableSet_Ioc
    have hdis : Pairwise (Function.onFun Disjoint I) := by
      simpa [hI] using pairwise_disjoint_Ioc_add_zsmul a d
    have hun : ⋃ n, I n = univ := by simpa [hI] using iUnion_Ioc_add_zsmul hd a
    have hs : ∀ F : Finset ℤ, ∑ n ∈ F, cut V (I n) u = cut V (⋃ n ∈ F, I n) u := by
      intro F
      induction F using Finset.induction_on with
      | empty => simp [(cutLaws (V := V) ∅ ∅ .empty .empty).2.2.2.2.1]
      | insert n F hn ih =>
        rw [Finset.sum_insert hn, ih, Finset.set_biUnion_insert,
          (cutLaws (V := V) (I n) _ measurableSet_Ioc (hm F)).2.2.1, ContinuousLinearMap.add_apply]
        exact disjoint_iUnion₂_right.2 fun k hk => hdis fun e => hn (e ▸ hk)
    have h1 := key (fun F : Finset ℤ => (⋃ n ∈ F, I n)ᶜ) (fun F => (hm F).compl)
      (fun F G h => compl_subset_compl.2 (biUnion_subset_biUnion_left h)) (by
        refine eq_empty_of_forall_notMem fun x hx => ?_
        obtain ⟨n, hn⟩ := mem_iUnion.1 (hun ▸ mem_univ x : x ∈ ⋃ n, I n)
        exact mem_iInter.1 hx {n} (by simpa using hn))
    rw [HasSum, tendsto_iff_norm_sub_tendsto_zero]
    refine h1.congr fun F => ?_
    obtain ⟨-, -, c3, c4, -⟩ := cutLaws (V := V) (⋃ n ∈ F, I n) (⋃ n ∈ F, I n)ᶜ (hm F) (hm F).compl
    have h2 := c3 disjoint_compl_right
    rw [union_compl_self, c4] at h2
    have h3 : u = cut V (⋃ n ∈ F, I n) u + cut V (⋃ n ∈ F, I n)ᶜ u := DFunLike.congr_fun h2 u
    rw [hs, norm_sub_rev, sub_eq_of_eq_add' h3]
