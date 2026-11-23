import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.KerNIdB

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.RgBcC.VC.KN

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contOn_avg (hLg : LgCpt) [MeasurableSpace (G n)] [BorelSpace (G n)] {N : Subgroup (G n)}
    (hNc : IsClosed (N : Set (G n))) (ν : Measure N) [IsFiniteMeasureOnCompacts ν] {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (h : Mat n → X) (hc : ContinuousOn h (GLs n)) (R : ℝ)
    (hR : ∀ y ∈ GLs n, R < lg y → h y = 0) :
    ContinuousOn (fun y => ∫ u : N, h ((u : G n).val * y) ∂ν) (GLs n) := by
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : FirstCountableTopology (Mat n) := inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  intro y₀ hy₀
  obtain ⟨K, hKn, hKs, hK⟩ := local_compact_nhds (isOpen_GLs.mem_nhds hy₀)
  obtain ⟨M, hM⟩ := hK.bddAbove_image (lg_contOn.mono hKs)
  set S : Set N := {u : N | lg ((u : G n) : Mat n) ≤ R + M} with hSdef
  have hS : IsCompact S := cptN hLg hNc (R + M)
  have hcu : Continuous (fun u : N => ((u : G n) : Mat n)) := by fun_prop
  set T : Set (Mat n) := (fun p : N × Mat n => ((p.1 : G n) : Mat n) * p.2) '' (S ×ˢ K) with hTdef
  have hT : IsCompact T := (hS.prod hK).image (by fun_prop)
  have hTs : T ⊆ GLs n := by
    rintro _ ⟨p, hp, rfl⟩
    exact mul_memGL _ _ (hKs hp.2)
  obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn (hc.mono hTs)
  have hlc : Continuous (fun u : N => lg ((u : G n) : Mat n)) :=
    lg_contOn.comp_continuous hcu (fun u => memGL _)
  have hSm : MeasurableSet S := (isClosed_le hlc continuous_const).measurableSet
  have hbound : ∀ y ∈ K, ∀ u : N, ‖h (((u : G n) : Mat n) * y)‖ ≤ S.indicator (fun _ => C) u := by
    intro y hy u
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu]
      exact hC _ ⟨(u, y), ⟨hu, hy⟩, rfl⟩
    · rw [Set.indicator_of_notMem hu]
      have hu' : ¬ lg ((u : G n) : Mat n) ≤ R + M := hu
      have hyM : lg y ≤ M := hM ⟨y, hy, rfl⟩
      have h1 := lg_le_of_mul ((u : G n) : Mat n) y (hKs hy)
      have h2 : R + M < lg ((u : G n) : Mat n) := lt_of_not_ge hu'
      rw [hR _ (mul_memGL _ _ (hKs hy)) (by linarith), norm_zero]
  apply continuousWithinAt_of_dominated (bound := S.indicator (fun _ => C))
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (integrable_N hLg hNc ν h hc R hR y hy).aestronglyMeasurable
  · filter_upwards [mem_nhdsWithin_of_mem_nhds hKn] with y hy
    exact Filter.Eventually.of_forall (hbound y hy)
  · exact (integrable_indicator_iff hSm).2 (integrableOn_const hS.measure_ne_top)
  · refine Filter.Eventually.of_forall (fun u => ?_)
    have hm : Continuous (fun y : Mat n => ((u : G n) : Mat n) * y) := by fun_prop
    exact (hc.comp hm.continuousOn (fun y hy => mul_memGL _ _ hy)) y₀ hy₀

theorem key (hLg : LgCpt) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (k B : Mat n → (E.V →L[ℂ] E.V)) (hkc : ContinuousOn k (GLs n)) (Rk : ℝ)
    (hkR : ∀ y ∈ GLs n, Rk < lg y → k y = 0) {N : Subgroup (G n)} (hNc : IsClosed (N : Set (G n)))
    (ν : Measure N) [ν.IsHaarMeasure] [ν.IsInvInvariant] (hBc : ContinuousOn B (GLs n))
    (hBN : ∀ u : N, ∀ y ∈ GLs n, B ((u : G n).val * y) = B y) (φ : Mat n → E.V) (hφc : ContinuousOn φ (GLs n))
    (Rφ : ℝ) (hφR : ∀ y ∈ GLs n, Rφ < lg y → φ y = 0) :
    ∫ y : G n, k y.val (B y.val (∫ u : N, φ ((u : G n).val * y.val) ∂ν)) ∂μ =
      ∫ y : G n, (∫ u : N, k ((u : G n).val * y.val) ∂ν) (B y.val (φ y.val)) ∂μ := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℂ)).symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (G n) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SigmaCompactSpace (G n) := ⟨⟨fun m : ℕ => {y : G n | lg y.val ≤ m}, fun m => hLg n m, by
    ext y
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exists_nat_ge _⟩⟩
  haveI : SigmaCompactSpace N := ⟨⟨fun m : ℕ => {u : N | lg ((u : G n) : Mat n) ≤ m},
    fun m => cptN hLg hNc m, by
    ext y
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exists_nat_ge _⟩⟩
  have iφ : ∀ y : G n, Integrable (fun u : N => φ ((u : G n).val * y.val)) ν := fun y =>
    integrable_N hLg hNc ν φ hφc Rφ hφR y.val (memGL y)
  have ik : ∀ y : G n, Integrable (fun u : N => k ((u : G n).val * y.val)) ν := fun y =>
    integrable_N hLg hNc ν k hkc Rk hkR y.val (memGL y)
  set F : G n → N → E.V := fun y u => k y.val (B y.val (φ ((u : G n).val * y.val))) with hF
  set H : G n → N → E.V := fun y u => k ((u : G n).val * y.val) (B y.val (φ y.val)) with hH
  have cu1 : Continuous (fun p : G n × N => p.1.val) := Units.continuous_val.comp continuous_fst
  have cu2 : Continuous (fun p : G n × N => ((p.2 : G n).val * p.1.val)) := by fun_prop
  have hB1 : Continuous (fun p : G n × N => B p.1.val) := hBc.comp_continuous cu1 (fun p => memGL _)
  have iF : Integrable (Function.uncurry F) (μ.prod ν) := by
    have cF : Continuous (Function.uncurry F) :=
      (hkc.comp_continuous cu1 (fun p => memGL _)).clm_apply
        (hB1.clm_apply (hφc.comp_continuous cu2 (fun p => mul_memGL _ _ (memGL _))))
    have KF : IsCompact ({y : G n | lg y.val ≤ Rk} ×ˢ {u : N | lg ((u : G n) : Mat n) ≤ Rk + Rφ}) :=
      (hLg n Rk).prod (cptN hLg hNc (Rk + Rφ))
    refine cF.integrable_of_hasCompactSupport (HasCompactSupport.intro KF ?_)
    rintro ⟨y, u⟩ hp
    simp only [Set.mem_prod, Set.mem_setOf_eq, not_and_or, not_le] at hp
    show k y.val (B y.val (φ ((u : G n).val * y.val))) = 0
    by_cases hy : lg y.val ≤ Rk
    · have hu : Rk + Rφ < lg ((u : G n) : Mat n) := by
        rcases hp with h | h
        · exact absurd hy (not_le.mpr h)
        · exact h
      have h1 := lg_le_of_mul ((u : G n) : Mat n) y.val (memGL y)
      rw [hφR _ (mul_memGL _ _ (memGL y)) (by linarith), map_zero, map_zero]
    · rw [hkR _ (memGL y) (lt_of_not_ge hy), ContinuousLinearMap.zero_apply]
  have iH : Integrable (Function.uncurry H) (μ.prod ν) := by
    have cH : Continuous (Function.uncurry H) :=
      (hkc.comp_continuous cu2 (fun p => mul_memGL _ _ (memGL _))).clm_apply
        (hB1.clm_apply (hφc.comp_continuous cu1 (fun p => memGL _)))
    have KH : IsCompact ({y : G n | lg y.val ≤ Rφ} ×ˢ {u : N | lg ((u : G n) : Mat n) ≤ Rk + Rφ}) :=
      (hLg n Rφ).prod (cptN hLg hNc (Rk + Rφ))
    refine cH.integrable_of_hasCompactSupport (HasCompactSupport.intro KH ?_)
    rintro ⟨y, u⟩ hp
    simp only [Set.mem_prod, Set.mem_setOf_eq, not_and_or, not_le] at hp
    show k ((u : G n).val * y.val) (B y.val (φ y.val)) = 0
    by_cases hy : lg y.val ≤ Rφ
    · have hu : Rk + Rφ < lg ((u : G n) : Mat n) := by
        rcases hp with h | h
        · exact absurd hy (not_le.mpr h)
        · exact h
      have h1 := lg_le_of_mul ((u : G n) : Mat n) y.val (memGL y)
      rw [hkR _ (mul_memGL _ _ (memGL y)) (by linarith), ContinuousLinearMap.zero_apply]
    · rw [hφR _ (memGL y) (lt_of_not_ge hy), map_zero, map_zero]
  have s1 : ∀ y : G n, k y.val (B y.val (∫ u : N, φ ((u : G n).val * y.val) ∂ν)) = ∫ u : N, F y u ∂ν := by
    intro y
    exact (ContinuousLinearMap.integral_comp_comm ((k y.val).comp (B y.val)) (iφ y)).symm
  have s6 : ∀ y : G n, (∫ u : N, k ((u : G n).val * y.val) ∂ν) (B y.val (φ y.val)) = ∫ u : N, H y u ∂ν :=
    fun y => ContinuousLinearMap.integral_apply (ik y) _
  have s3 : ∀ u : N, ∫ y : G n, F y u ∂μ = ∫ y : G n, H y u⁻¹ ∂μ := by
    intro u
    rw [← integral_mul_left_eq_self (μ := μ) (fun x : G n => H x u⁻¹) (u : G n)]
    congr 1
    ext x
    have e1 : (((u⁻¹ : N) : G n)).val * (((u : G n) * x)).val = x.val := by
      rw [← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel_left]
    have e2 : B (((u : G n) * x)).val = B x.val := by
      rw [Units.val_mul]
      exact hBN u x.val (memGL x)
    simp only [hF, hH]
    rw [e1, e2, Units.val_mul]
  calc ∫ y : G n, k y.val (B y.val (∫ u : N, φ ((u : G n).val * y.val) ∂ν)) ∂μ
      = ∫ y : G n, ∫ u : N, F y u ∂ν ∂μ := integral_congr_ae (Filter.Eventually.of_forall s1)
    _ = ∫ u : N, ∫ y : G n, F y u ∂μ ∂ν := integral_integral_swap iF
    _ = ∫ u : N, ∫ y : G n, H y u⁻¹ ∂μ ∂ν := integral_congr_ae (Filter.Eventually.of_forall s3)
    _ = ∫ u : N, ∫ y : G n, H y u ∂μ ∂ν := integral_inv_eq_self (fun u => ∫ y : G n, H y u ∂μ) ν
    _ = ∫ y : G n, ∫ u : N, H y u ∂ν ∂μ := (integral_integral_swap iH).symm
    _ = ∫ y : G n, (∫ u : N, k ((u : G n).val * y.val) ∂ν) (B y.val (φ y.val)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun y => (s6 y).symm))

end PositivityTheory.RgBcC.VC.KN
