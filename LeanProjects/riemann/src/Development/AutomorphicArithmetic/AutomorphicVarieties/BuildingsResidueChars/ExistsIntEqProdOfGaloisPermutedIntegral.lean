import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRatOfForallComplexRingEquivFixed
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

theorem UpperTheory.exists_int_eq_prod_of_galois_permuted_integral :
    ∀ (T : Type) [Fintype T] (f : T → ℂ), (∀ t, IsIntegral ℤ (f t)) → (∀ σ : ℂ ≃+* ℂ, ∃ u : T ≃ T, ∀ t, f (u t) = σ (f t)) → ∃ n : ℤ, (n : ℂ) = ∏ t, f t := by
  intro T _ f hf hσ
  have hfix : ∀ σ : ℂ ≃+* ℂ, σ (∏ t, f t) = ∏ t, f t := by
    intro σ
    obtain ⟨u, hu⟩ := hσ σ
    rw [map_prod, ← Equiv.prod_comp u f]
    exact Finset.prod_congr rfl (fun t _ => (hu t).symm)
  have hint : IsIntegral ℤ (∏ t, f t) := IsIntegral.prod f (fun t _ => hf t)
  obtain ⟨q, hq⟩ := GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed _ hfix
  have hq' : algebraMap ℚ ℂ q = ∏ t, f t := by simpa using hq.symm
  rw [← hq'] at hint
  have hqi : IsIntegral ℤ q := (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).mp hint
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (K := ℚ) hqi
  refine ⟨n, ?_⟩
  rw [← hq', ← hn]
  simp
