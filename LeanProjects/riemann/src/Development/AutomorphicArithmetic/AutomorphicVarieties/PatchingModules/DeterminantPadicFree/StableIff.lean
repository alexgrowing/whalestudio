import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DiscStIff

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.Det.stableIff :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (q : PrimeSpectrum B.B), B.IsStable q ↔ DiscSt B.u.D q.asIdeal := by
  intro l _ F O _ _ _ n r B q
  have hk : RingHom.ker (B.toKap q) = q.asIdeal := by
    rw [UniversalOrdinaryDeterminantRing.toKap, RingHom.ker_comp_of_injective _
      (algebraMap q.asIdeal.ResidueField (B.kap q)).injective,
      Ideal.ker_algebraMap_residueField]
  rw [← hk, Det.discStIff]
  rfl
