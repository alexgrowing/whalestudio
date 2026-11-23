import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaSuppBc

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.pmFib :
    ∀ (R σ : Type) [CommRing R] [IsNoetherianRing R] [Fintype σ] (y : σ → R) (f : R) (ii : Ideal R) (X : Type) [AddCommGroup X] [Module R X] [Module.Finite R X] (P : PMod y f ii X) (B : Type) [CommRing B] [Algebra P.BB B] (Q : Ideal B), Q.IsPrime → (∀ a, algebraMap P.BB B (algebraMap R P.BB (y a)) ∈ Q) → (Module.annihilator B (B ⊗[P.BB] P.MM) ≤ Q ↔ Module.annihilator R X ≤ (Q.comap (algebraMap P.BB B)).comap (algebraMap R P.BB)) := by
  intro R σ _ _ _ y f ii X _ _ _ P B _ _ Q hQ hy
  haveI := P.fin
  let Qp : PrimeSpectrum B := ⟨Q, hQ⟩
  let q := PrimeSpectrum.comap (algebraMap P.BB B) Qp
  have h1 := Module.mem_support_iff_of_finite (R := B) (M := B ⊗[P.BB] P.MM) (p := Qp)
  have h2 := mem_support_baseChange P.BB B P.MM Qp
  have h3 := Module.support_quotient (R := P.BB) (M := P.MM)
    (Ideal.span (Set.range fun a => algebraMap R P.BB (y a)))
  have h4 := P.fib.support_eq
  have h5 := mem_support_baseChange R P.BB X q
  have h6 := Module.mem_support_iff_of_finite (R := R) (M := X) (p := PrimeSpectrum.comap (algebraMap R P.BB) q)
  have hz : q ∈ PrimeSpectrum.zeroLocus (Ideal.span (Set.range fun a => algebraMap R P.BB (y a)) : Set P.BB) := by
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    exact hy a
  calc Module.annihilator B (B ⊗[P.BB] P.MM) ≤ Q ↔ Qp ∈ Module.support B (B ⊗[P.BB] P.MM) := h1.symm
    _ ↔ q ∈ Module.support P.BB P.MM := h2
    _ ↔ q ∈ Module.support P.BB (P.MM ⧸ (Ideal.span (Set.range fun a => algebraMap R P.BB (y a)) • ⊤ : Submodule P.BB P.MM)) := by
      rw [h3]
      exact ⟨fun h => ⟨h, hz⟩, fun h => h.1⟩
    _ ↔ q ∈ Module.support P.BB (P.BB ⊗[R] X) := by rw [h4]
    _ ↔ PrimeSpectrum.comap (algebraMap R P.BB) q ∈ Module.support R X := h5
    _ ↔ _ := h6
