import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.LocUApply
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionApplyEquivariantEq
import Development.AutomorphicArithmetic.TwistedTraces.FixedProjectionInvariantAndCommutingReps

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.inf_fixed_le_spanFix_of_dense_spanAll :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (_ : GroundTheory.Automorphic.IsSmooth τ) (π : UnitaryRep G H) (U : Subgroup G) (_ : IsCompact (U : Set G)) (_ : IsOpen (U : Set G)) (V D : Submodule ℂ H), IsClosed (D : Set H) → π.IsInvariant D → D ≤ V → V ≤ (spanAll τ π V).topologicalClosure → FiniteDimensional ℂ ↥(D ⊓ fixU π U) → D ⊓ fixU π U ≤ spanFix τ π D U := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ π U hUc hUo V D hD hinv hDV hV hfin y hy
  have hQX : spanFix τ π D U ≤ D ⊓ fixU π U := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, x, hx, rfl⟩
    exact ⟨hf.mem x, fun u hu => by rw [← hf.map, hx u hu]⟩
  haveI : FiniteDimensional ℂ ↥(spanFix τ π D U) := Submodule.finiteDimensional_of_le hQX
  have hQc : IsClosed (spanFix τ π D U : Set H) := Submodule.closed_of_finiteDimensional _
  have hc : D.topologicalClosure = D := hD.submodule_topologicalClosure_eq
  have hpm : ∀ v, prj D v ∈ D := fun v => by
    have h : prj D v ∈ D.topologicalClosure := Submodule.starProjection_apply_mem _ v
    rwa [hc] at h
  have hpc : ∀ g v, π g (prj D v) = prj D (π g v) := fun g v => by
    have hi : π.IsInvariant D.topologicalClosure := by rw [hc]; exact hinv
    exact congrArg (fun T : H →L[ℂ] H => T v)
      ((UnitaryRep.isInvariant_iff_commute_starProjection D.topologicalClosure).1 hi g).eq
  let Φ : H →L[ℂ] H := prj (fixU π U) ∘L prj D
  have hspan : spanAll τ π V ≤ (spanFix τ π D U).comap (Φ : H →ₗ[ℂ] H) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨f, hf, x, rfl⟩
    let f' : S →ₗ[ℂ] H := (prj D : H →ₗ[ℂ] H) ∘ₗ f
    have hmap : ∀ g x, f' (τ g x) = π g (f' x) := fun g x => by
      show prj D (f (τ g x)) = π g (prj D (f x))
      rw [hf.map, hpc]
    have hf1 : Eqv τ π D f' := ⟨fun x => hpm _, hmap⟩
    have hf2 : Eqv τ π ⊤ f' := ⟨fun _ => trivial, hmap⟩
    have h := UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π U hUc hUo f' hf2 x
    show prj (fixU π U) (prj D (f x)) ∈ spanFix τ π D U
    have h' : prj (fixU π U) (prj D (f x)) = f' (fixedProj τ hτ hUc hUo x) := h
    rw [h']
    exact Submodule.subset_span ⟨f', hf1, _, (fixedProj τ hτ hUc hUo x).2, rfl⟩
  have hcl : (spanAll τ π V).topologicalClosure ≤ (spanFix τ π D U).comap (Φ : H →ₗ[ℂ] H) :=
    Submodule.topologicalClosure_minimal _ hspan (hQc.preimage Φ.continuous)
  have hy' : Φ y ∈ spanFix τ π D U := hcl (hV (hDV hy.1))
  have hp : prj D y = y := Submodule.starProjection_eq_self_iff.2 (D.le_topologicalClosure hy.1)
  have he : prj (fixU π U) y = y := (UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π U U).2.1 y hy.2
  have hΦ : Φ y = y := by
    show prj (fixU π U) (prj D y) = y
    rw [hp, he]
  rwa [hΦ] at hy'
