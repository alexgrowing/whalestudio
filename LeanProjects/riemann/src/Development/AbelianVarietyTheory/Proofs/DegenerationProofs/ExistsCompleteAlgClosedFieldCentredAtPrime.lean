import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteIsAlgClosedCExt

namespace GlobalTheory.Ex

theorem exists_complete_isAlgClosed_centred_at_prime :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [FaithfulSMul R K] [Algebra.IsAlgebraic R K] (P : Ideal R), P.IsPrime → P ≠ ⊥ → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (gam : K →+* C), (∀ r, ‖gam (algebraMap R K r)‖ ≤ 1) ∧ ∀ r ∈ P, ‖gam (algebraMap R K r)‖ < 1 := by
  intro R K _ _ _ _ _ _ _ P hP hP0
  obtain ⟨O, _, _, _, _, φ, hker, hcom⟩ :=
    GlobalTheory.exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) P (bot_lt_iff_ne_bot.2 hP0)
  have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  obtain ⟨C, i1, i2, i3, i4, i5, -, -, h1, h2⟩ :=
    GlobalTheory.Ex.exists_complete_isAlgClosed_cExt O (FractionRing O)
  let ψ : R →+* C := (algebraMap (FractionRing O) C).comp ((algebraMap O (FractionRing O)).comp φ)
  have hψ : Function.Injective ψ :=
    (algebraMap (FractionRing O) C).injective.comp
      ((IsFractionRing.injective O (FractionRing O)).comp hφ)
  letI : Algebra R C := ψ.toAlgebra
  haveI : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).2 hψ
  let g : K →ₐ[R] C := IsAlgClosed.lift
  have hg : ∀ r, g.toRingHom (algebraMap R K r) = ψ r := fun r => g.commutes r
  refine ⟨C, i1, i2, i3, i4, g.toRingHom, fun r => ?_, fun r hr => ?_⟩
  · rw [hg]
    exact h1 (φ r)
  · rw [hg]
    exact h2 (φ r) (by rw [← hcom] at hr; exact hr)

end GlobalTheory.Ex
