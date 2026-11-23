import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C

section Generic

variable {G H : Type*} [Group G] [TopologicalSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (π : UnitaryRep G H) (W : Submodule ℂ H) [CompleteSpace W]
  (hWi : π.IsInvariant W)

private theorem isSummandOf_map (hWc : IsClosed (W : Set H))
    (V : Submodule ℂ W) [CompleteSpace V] (hinv : (π.restrict W hWi).IsInvariant V)
    (hirr : ((π.restrict W hWi).restrict V hinv).IsIrreducible) :
    IsSummandOf π W (V.map W.subtype) := by
  have hVc : IsClosed (V : Set W) :=
    (completeSpace_coe_iff_isComplete.1 ‹CompleteSpace V›).isClosed
  have hemb : Topology.IsClosedEmbedding ((↑) : W → H) := hWc.isClosedEmbedding_subtypeVal
  refine ⟨Submodule.map_subtype_le _ _, ?_, ?_, ?_, ?_⟩
  · have h := hemb.isClosedMap _ hVc
    simpa [Submodule.map_coe] using h
  · rintro g _ ⟨w, hw, rfl⟩
    exact ⟨π.restrict W hWi g w, hinv g w hw, rfl⟩
  · haveI := hirr.1
    obtain ⟨w, hw0⟩ := exists_ne (0 : V)
    intro hb
    have hm : ((w : W) : H) ∈ V.map W.subtype := ⟨w.1, w.2, rfl⟩
    rw [hb, Submodule.mem_bot] at hm
    exact hw0 (Subtype.ext (Subtype.ext hm))
  · intro V' hle hcl hinv'
    have hYc : IsClosed (((V'.comap W.subtype).comap V.subtype : Submodule ℂ V) : Set V) :=
      hcl.preimage (continuous_subtype_val.comp continuous_subtype_val)
    have hYi : ((π.restrict W hWi).restrict V hinv).IsInvariant
        ((V'.comap W.subtype).comap V.subtype) := fun g v hv => hinv' g _ hv
    rcases hirr.2 _ hYc hYi with h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨w, hw, rfl⟩ := hle hx
      have hm : (⟨w, hw⟩ : V) ∈ (V'.comap W.subtype).comap V.subtype := hx
      rw [h, Submodule.mem_bot] at hm
      have h0 : w = 0 := congrArg Subtype.val hm
      simp [h0]
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨w, hw, rfl⟩
      have hm : (⟨w, hw⟩ : V) ∈ (V'.comap W.subtype).comap V.subtype := h ▸ Submodule.mem_top
      exact hm

private theorem closure_iSup_summands (hWc : IsClosed (W : Set H))
    (s : Set (Submodule ℂ W)) [∀ V : s, CompleteSpace (V : Submodule ℂ W)]
    (hinv : ∀ V : s, (π.restrict W hWi).IsInvariant V)
    (hH : IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ W)) (fun V => (V : Submodule ℂ W).subtypeₗᵢ))
    (hirr : ∀ V : s, ((π.restrict W hWi).restrict V (hinv V)).IsIrreducible) :
    (⨆ V : {V // IsSummandOf π W V}, V.1).topologicalClosure = W := by
  have hmain : ∀ V : s, IsSummandOf π W ((V : Submodule ℂ W).map W.subtype) :=
    fun V => isSummandOf_map π W hWi hWc V.1 (hinv V) (hirr V)
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (iSup_le fun V => V.2.le) hWc
  · set S : Submodule ℂ H := ⨆ V : {V // IsSummandOf π W V}, V.1 with hS
    have hcl : IsClosed ((S.topologicalClosure.comap W.subtype : Submodule ℂ W) : Set W) :=
      S.isClosed_topologicalClosure.preimage continuous_subtype_val
    have hle : (⨆ V : s, LinearMap.range ((V : Submodule ℂ W).subtypeₗᵢ).toLinearMap) ≤
        S.topologicalClosure.comap W.subtype := by
      refine iSup_le fun V => ?_
      rintro _ ⟨w, rfl⟩
      exact S.le_topologicalClosure
        (le_iSup (fun V : {V // IsSummandOf π W V} => V.1) ⟨_, hmain V⟩ ⟨w.1, w.2, rfl⟩)
    have htop : (⊤ : Submodule ℂ W) ≤ S.topologicalClosure.comap W.subtype := by
      have h := Submodule.topologicalClosure_minimal _ hle hcl
      rw [← hH.OrthogonalFamily.range_linearIsometry,
        LinearMap.range_eq_top.2 hH.surjective_isometry] at h
      exact h
    intro x hx
    exact htop (Submodule.mem_top : (⟨x, hx⟩ : W) ∈ ⊤)

end Generic

theorem UpperTheory.ConvolutionTheory.C.summandsSpan :
    UpperTheory.ConvolutionTheory.C.SummandsSpan := by
  intro K _ _ n μ _
  obtain ⟨s, hc, hinv, hH, hirr⟩ := exists_isHilbertSum_isIrreducible_cuspidal μ
  haveI := hc
  exact closure_iSup_summands (rightRegularRep (rationalGLOne K n) μ) (cuspidalL2 μ)
    (isInvariant_cuspidalL2 μ) (isClosed_cuspidalL2 μ) s hinv hH hirr
