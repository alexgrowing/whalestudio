import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralExtensionAlgClosed

private theorem UpperTheory.exists_ringHom_extension_of_integral (R S K : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Field K] [IsAlgClosed K]
    (hinj : Function.Injective (algebraMap R S)) (b : R →+* K) :
    ∃ Φ : S →+* K, Φ.comp (algebraMap R S) = b :=
  _root_.UpperTheory.Reformulated.B.IntegralExtensionAlgClosed.exists_ringHom_extension_of_integral R S K hinj b

theorem UpperTheory.exists_valuation_extension_integral :
    ∀ (R S K : Type) [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] [Field K] [IsAlgClosed K] (V : ValuationSubring K), Function.Injective (algebraMap R S) → ∀ b : R →+* V, ∃ Φ : S →+* V, Φ.comp (algebraMap R S) = b := by
  intro R S K _ _ _ _ _ _ V hinj b
  obtain ⟨Φ, hΦ⟩ := UpperTheory.exists_ringHom_extension_of_integral R S K hinj ((algebraMap V K).comp b)
  have hmem : ∀ s : S, Φ s ∈ V := by
    intro s
    have hs : IsIntegral R s := Algebra.IsIntegral.isIntegral s
    have h2 : IsIntegral V (Φ s) := hs.map_of_comp_eq b Φ hΦ.symm
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := V) (K := K)).1 h2
    rw [← hy]; exact y.2
  refine ⟨Φ.codRestrict V hmem, ?_⟩
  ext r
  exact RingHom.congr_fun hΦ r
