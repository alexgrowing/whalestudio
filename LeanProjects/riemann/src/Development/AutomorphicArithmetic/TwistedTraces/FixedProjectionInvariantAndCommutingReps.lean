import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf
open scoped InnerProductSpace

private theorem prj_mem_of_closed {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (v : H) : prj V v ∈ V := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have h : prj V v ∈ V.topologicalClosure := Submodule.starProjection_apply_mem _ v
  rwa [hc] at h

private theorem prj_eq_of_mem {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) {v : H} (hv : v ∈ V) : prj V v = v :=
  Submodule.starProjection_eq_self_iff.2 (V.le_topologicalClosure hv)

private theorem prj_adjoint {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) : ContinuousLinearMap.adjoint (prj V) = prj V :=
  (ContinuousLinearMap.isSelfAdjoint_iff'.1 (isSelfAdjoint_starProjection V.topologicalClosure))

private theorem prj_commute {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (T : H →L[ℂ] H) (h1 : ∀ v ∈ V, T v ∈ V)
    (h2 : ∀ v ∈ V, ContinuousLinearMap.adjoint T v ∈ V) (v : H) : prj V (T v) = T (prj V v) := by
  have hc : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have hm : ∀ v, v ∈ V.topologicalClosure ↔ v ∈ V := fun v => by rw [hc]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    ((hm _).2 (h1 _ (prj_mem_of_closed V hV v))) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact Submodule.starProjection_inner_eq_zero v _ ((hm _).2 (h2 w ((hm _).1 hw)))

private theorem prj_fix_commute {G H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (U : Subgroup G) (T : H →L[ℂ] H)
    (h1 : ∀ g v, π g (T v) = T (π g v))
    (h2 : ∀ g v, π g (ContinuousLinearMap.adjoint T v) = ContinuousLinearMap.adjoint T (π g v)) (v : H) :
    prj (fixU π U) (T v) = T (prj (fixU π U) v) :=
  prj_commute _ (isClosed_fixU π U) T
    (fun v hv u hu => by rw [h1, mem_fixU.1 hv u hu])
    (fun v hv u hu => by rw [h2, mem_fixU.1 hv u hu]) v

theorem UpperTheory.fixedProjection_invariant_and_commuting_reps :
    ∀ (G G' H : Type) [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep G H) (π' : UnitaryRep G' H) (U : Subgroup G) (U' : Subgroup G'), (∀ v, prj (fixU π U) v ∈ fixU π U) ∧ (∀ v ∈ fixU π U, prj (fixU π U) v = v) ∧ (∀ (D : Submodule ℂ H), IsClosed (D : Set H) → π.IsInvariant D → ∀ v ∈ D, prj (fixU π U) v ∈ D) ∧ ((∀ g h v, π g (π' h v) = π' h (π g v)) → (∀ h v, prj (fixU π U) (π' h v) = π' h (prj (fixU π U) v)) ∧ ∀ v, prj (fixU π U) (prj (fixU π' U') v) = prj (fixU π' U') (prj (fixU π U) v)) := by
  intro G G' H _ _ _ _ _ _ _ π π' U U'
  refine ⟨prj_mem_of_closed _ (isClosed_fixU π U), fun v hv => prj_eq_of_mem _ hv, ?_, ?_⟩
  · intro D hD hinv v hv
    have hc : D.topologicalClosure = D := hD.submodule_topologicalClosure_eq
    have hcomm : ∀ g v, π g (prj D v) = prj D (π g v) := fun g v => by
      have hi : π.IsInvariant D.topologicalClosure := by rw [hc]; exact hinv
      exact congrArg (fun T : H →L[ℂ] H => T v)
        ((UnitaryRep.isInvariant_iff_commute_starProjection D.topologicalClosure).1 hi g).eq
    have h := prj_fix_commute π U (prj D) hcomm (fun g v => by rw [prj_adjoint]; exact hcomm g v) v
    rw [prj_eq_of_mem D hv] at h
    rw [h]
    exact prj_mem_of_closed D hD _
  · intro hc
    have h4 : ∀ h v, prj (fixU π U) (π' h v) = π' h (prj (fixU π U) v) := fun h v =>
      prj_fix_commute π U (π' h) (fun g v => hc g h v)
        (fun g v => by rw [UnitaryRep.adjoint_map]; exact hc g h⁻¹ v) v
    refine ⟨h4, fun v => ?_⟩
    have h4' : ∀ g v, prj (fixU π' U') (π g v) = π g (prj (fixU π' U') v) := fun g v =>
      prj_fix_commute π' U' (π g) (fun h v => (hc g h v).symm)
        (fun h v => by rw [UnitaryRep.adjoint_map]; exact (hc g⁻¹ h v).symm) v
    exact prj_fix_commute π U (prj (fixU π' U')) (fun g v => (h4' g v).symm)
      (fun g v => by rw [prj_adjoint]; exact (h4' g v).symm) v
