import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

private theorem exists_adapted {H ι : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : ι → Submodule ℂ H) (hc : ∀ i, IsClosed (U i : Set H)) (ho : Pairwise fun i j => U i ⟂ U j)
    (ht : ∀ x : H, (∀ i, x ∈ (U i)ᗮ) → x = 0) :
    ∃ (κ : ι → Type) (b : HilbertBasis (Σ i, κ i) ℂ H), ∀ i k, b ⟨i, k⟩ ∈ U i := by
  haveI : ∀ i, CompleteSpace (U i) := fun i => (hc i).completeSpace_coe
  choose w b hb using fun i => exists_hilbertBasis ℂ (U i)
  have hfam : OrthogonalFamily ℂ (fun i => U i) fun i => (U i).subtypeₗᵢ :=
    OrthogonalFamily.of_pairwise ho
  have hon : Orthonormal ℂ fun a : Σ i, w i => (U a.1).subtypeₗᵢ (b a.1 a.2) :=
    hfam.orthonormal_sigma_orthonormal fun i => (b i).orthonormal
  have hsp : (Submodule.span ℂ (Set.range fun a : Σ i, w i => (U a.1).subtypeₗᵢ (b a.1 a.2)))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    refine ht x fun i => ?_
    rw [Submodule.mem_orthogonal']
    intro u hu
    have h1 := ((innerSL ℂ x).comp (U i).subtypeL).hasSum ((b i).hasSum_repr ⟨u, hu⟩)
    have h2 : ∀ k, inner ℂ x ((b i k : U i) : H) = 0 := fun k =>
      (Submodule.mem_orthogonal' _ _).1 hx _ (Submodule.subset_span ⟨⟨i, k⟩, rfl⟩)
    simp only [map_smul, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply, innerSL_apply_apply, h2,
      smul_zero] at h1
    exact h1.unique hasSum_zero
  refine ⟨fun i => w i, HilbertBasis.mkOfOrthogonalEqBot hon hsp, fun i k => ?_⟩
  rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact (b i k).2

private theorem inner_prj {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) (T : H →L[ℂ] H) (x : H) :
    inner ℂ x ((prj V ∘L T ∘L prj V) x) = inner ℂ (prj V x) (T (prj V x)) := by
  simp only [ContinuousLinearMap.comp_apply, prj]
  exact (Submodule.inner_starProjection_left_eq_right _ _ _).symm

theorem UpperTheory.ConvolutionTheory.C.traceSum :
    UpperTheory.ConvolutionTheory.C.TraceSum := by
  intro H ι _ _ _ V T ho hT
  set W := ⨆ i, V i with hW
  let U : Option ι → Submodule ℂ H := fun o => o.elim W.topologicalClosureᗮ fun i => (V i).topologicalClosure
  have hle : ∀ i, (V i).topologicalClosure ≤ W.topologicalClosure := fun i =>
    Submodule.topologicalClosure_mono (le_iSup V i)
  have hoU : Pairwise fun i j => U i ⟂ U j := by
    rintro (_ | i) (_ | j) hij
    · exact absurd rfl hij
    · exact (Submodule.isOrtho_orthogonal_left _).mono_right (hle j)
    · exact (Submodule.isOrtho_orthogonal_right _).mono_left (hle i)
    · have h := ho (fun e => hij (congrArg some e) : i ≠ j)
      change (V i).topologicalClosure ≤ (V j).topologicalClosureᗮ
      rw [Submodule.orthogonal_closure]
      exact Submodule.topologicalClosure_minimal _ h (Submodule.isClosed_orthogonal _)
  obtain ⟨κ, b, hb⟩ := exists_adapted U (by
      rintro (_ | i)
      · exact Submodule.isClosed_orthogonal _
      · exact Submodule.isClosed_topologicalClosure _) hoU (by
      intro x hx
      have h1 : x ∈ W.topologicalClosureᗮ := by
        rw [Submodule.orthogonal_closure, hW, ← Submodule.iInf_orthogonal, Submodule.mem_iInf]
        intro i
        have := hx (some i)
        change x ∈ (V i).topologicalClosureᗮ at this
        rwa [Submodule.orthogonal_closure] at this
      exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 (hx none) x h1))
  have hWs : ∀ i k, prj W (b ⟨some i, k⟩) = b ⟨some i, k⟩ := fun i k =>
    Submodule.starProjection_eq_self_iff.2 (hle i (hb (some i) k))
  have hWn : ∀ k, prj W (b ⟨none, k⟩) = 0 := fun k =>
    (Submodule.starProjection_apply_eq_zero_iff _).2 (hb none k)
  have hVs : ∀ i k, prj (V i) (b ⟨some i, k⟩) = b ⟨some i, k⟩ := fun i k =>
    Submodule.starProjection_eq_self_iff.2 (hb (some i) k)
  have hVn : ∀ i o k, o ≠ some i → prj (V i) (b ⟨o, k⟩) = 0 := fun i o k h =>
    (Submodule.starProjection_apply_eq_zero_iff _).2 (hoU h (hb o k))
  have htc : ∀ i, IsTraceClass (prj (V i) ∘L T ∘L prj (V i)) := fun i => by
    have e1 : prj (V i) ∘L prj W = prj (V i) := Submodule.starProjection_comp_starProjection_of_le (hle i)
    have e2 : ∀ x, prj W (prj (V i) x) = prj (V i) x := fun x =>
      Submodule.starProjection_eq_self_iff.2 (hle i (Submodule.starProjection_apply_mem _ _))
    have e3 : ∀ x, prj (V i) (prj W x) = prj (V i) x := fun x => DFunLike.congr_fun e1 x
    have := (hT.comp_left (prj (V i))).comp_right (prj (V i))
    convert this using 1
    ext x
    simp only [ContinuousLinearMap.comp_apply, e2, e3]
  have h0 := hT.hasSum_trace b
  simp only [inner_prj] at h0
  have h1 : HasSum (fun o : Option ι => o.elim 0 fun i => trOn (V i) T) (trOn W T) := by
    refine h0.sigma ?_
    rintro (_ | i)
    · simpa only [hWn, inner_zero_left, Option.elim_none] using hasSum_zero
    · have h2 := (htc i).hasSum_trace b
      simp only [inner_prj] at h2
      rw [← (sigma_mk_injective (i := some i)).hasSum_iff] at h2
      · simpa only [Function.comp_def, hVs, hWs, Option.elim_some, trOn] using h2
      · rintro ⟨o, k⟩ hk
        rw [hVn i o k, inner_zero_left]
        rintro rfl
        exact hk ⟨k, rfl⟩
  rw [← (Option.some_injective ι).hasSum_iff] at h1
  · exact h1
  · rintro (_ | i) h
    · rfl
    · exact absurd ⟨i, rfl⟩ h
