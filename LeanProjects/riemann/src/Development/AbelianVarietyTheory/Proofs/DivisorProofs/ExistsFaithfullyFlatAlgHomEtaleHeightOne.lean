import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfullyFlatAdicCompletionSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomQuotientSpanPowEqOfEtaleLowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgHomQuotientPowLiftingPointStatement
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.GoodEtaleSection

theorem exists_faithfullyFlat_algHom : ∀ (A R C : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra A R] [CommRing C] [Algebra R C]
    (ρ : R →+* A), ρ.comp (algebraMap A R) = RingHom.id A →
    ∀ t : R, RingHom.ker ρ = Ideal.span {t} → t ∈ nonZeroDivisors R →
    Algebra.IsIntegral R C → GlobalTheory.GoodEtale.EtaleLow A R C →
    (∃ s : C →+* FractionRing A, s.comp (algebraMap R C) = (algebraMap A (FractionRing A)).comp ρ) →
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra R O), Module.FaithfullyFlat R O ∧ Nonempty (C →ₐ[R] O) := by
  intro A R C _ _ _ _ _ _ _ _ _ _ ρ hρ t hker ht hint hEt hs
  obtain ⟨s, hs⟩ := hs
  have ht0 : ρ t = 0 := RingHom.mem_ker.1 (hker ▸ Ideal.mem_span_singleton_self t)
  have htm : t ∈ maximalIdeal R := by
    by_contra h
    have hu : IsUnit (ρ t) := ((IsLocalRing.notMem_maximalIdeal.1 h)).map ρ
    rw [ht0] at hu
    exact not_isUnit_zero hu
  obtain ⟨g, -, hg⟩ := exists_integral_point A R C ρ hint s hs
  choose f hf using GlobalTheory.T.exists_algHom_quotient_pow_lifting_point A R C ρ hρ t hker ht hEt g hg
  have compat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := Ideal.span {t}) hle)).comp (f n) = f m := by
    intro m n hle
    refine GlobalTheory.T.algHom_quotient_span_pow_eq_of_etaleLow A R C ρ hρ t hker ht hEt m _ _ fun c => ?_
    set φ := Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (I := Ideal.span {t}) hle)
    have h1 := hf n c
    have h2 := hf m c
    rw [Ideal.mem_span_singleton] at h1 h2 ⊢
    have h1' := map_dvd φ h1
    have e1 : φ (Ideal.Quotient.mk (Ideal.span {t} ^ n) t) = Ideal.Quotient.mk (Ideal.span {t} ^ m) t := rfl
    have e2 : φ (Ideal.Quotient.mk (Ideal.span {t} ^ n) (algebraMap A R (g c))) =
        Ideal.Quotient.mk (Ideal.span {t} ^ m) (algebraMap A R (g c)) := rfl
    rw [map_sub, e1, e2] at h1'
    have := dvd_sub h1' h2
    simpa using this
  exact ⟨AdicCompletion (Ideal.span {t}) R, inferInstance, inferInstance,
    faithfullyFlat_adicCompletion_span R t htm, ⟨AdicCompletion.liftAlgHom _ f compat⟩⟩

end GlobalTheory.GoodEtaleSection
