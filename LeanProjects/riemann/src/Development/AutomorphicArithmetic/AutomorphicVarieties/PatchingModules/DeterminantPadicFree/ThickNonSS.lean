import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.thickNonSS :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (q : PrimeSpectrum B.B), B.IsThick q → NonSS (augmentationIdealKernel B.u) (RingHom.id B.B) q.asIdeal := by
  intro l _ F O _ _ _ n r B q h
  have he : augmentationIdealKernel B.u = (B.GroupAlgebraKernelIdeal : Set (MonoidAlgebra B.B F.G₀)) := by
    have : B.u.D.chBar (pairGens B.u) = B.GroupAlgebraKernelIdeal := by
      unfold UniversalOrdinaryDeterminantRing.GroupAlgebraKernelIdeal UniversalOrdinaryDeterminantRing.E0gens GDet.chBar pairGens
      rw [Set.union_assoc]
    unfold augmentationIdealKernel
    rw [this]
    rfl
  refine ⟨B.kap q, inferInstance, B.toKap q, ?_, ?_⟩
  · ext x
    unfold UniversalOrdinaryDeterminantRing.toKap
    rw [RingHom.mem_ker, RingHom.comp_apply, map_eq_zero, Ideal.algebraMap_residueField_eq_zero]
  · rw [RingHom.comp_id, he]
    exact h.2
