import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal

open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CompanionTheory.AdeleDen

private theorem natCast_mul_mem_intAd {F : Type} [Field F] [NumberField F] (m : ℕ)
    {a : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F} (ha : a ∈ PI.AdCpctDenWork.intAd F) :
    (m : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) * a ∈ PI.AdCpctDenWork.intAd F := by
  rw [PI.AdCpctDenWork.mem_intAd] at ha ⊢
  intro v
  rw [PI.AdCpctDenWork.natCast_mul_apply]
  exact mul_mem (PI.AdCpctDenWork.natCast_mem_int v m) (ha v)

theorem exists_common_denominator :
    ∀ (E : Type) [Field E] [NumberField E] (Q : Set (Af E)), IsCompact Q →
    ∃ D : ℕ, D ≠ 0 ∧ ∀ x : E, algebraMap E (Af E) x ∈ Q → ∃ r : 𝓞 E, (r : E) = D * x := by
  intro E _ _ Q hQ
  let U : ℕ → Set (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) := fun N =>
    {a | ((N.factorial : ℕ) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) * a ∈ PI.AdCpctDenWork.intAd E}
  have hUo : ∀ N, IsOpen (U N) := fun N =>
    (continuous_const.mul continuous_id).isOpen_preimage _ PI.AdCpctDenWork.isOpen_intAd
  have hUc : Q ⊆ ⋃ N, U N := by
    intro a _
    obtain ⟨m, hm, hma⟩ := PI.AdCpctDenWork.exists_nat_adele a
    refine Set.mem_iUnion.2 ⟨m, ?_⟩
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hm le_rfl
    show ((m.factorial : ℕ) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) * a ∈ PI.AdCpctDenWork.intAd E
    rw [hk, Nat.cast_mul, mul_comm (m : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E), mul_assoc]
    exact natCast_mul_mem_intAd k hma
  have hUd : Directed (· ⊆ ·) U := by
    refine Monotone.directed_le ?_
    intro N M hNM a ha
    obtain ⟨k, hk⟩ := Nat.factorial_dvd_factorial hNM
    show ((M.factorial : ℕ) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) * a ∈ PI.AdCpctDenWork.intAd E
    rw [hk, Nat.cast_mul, mul_comm ((N.factorial : ℕ) : IsDedekindDomain.FiniteAdeleRing (𝓞 E) E), mul_assoc]
    exact natCast_mul_mem_intAd k ha
  obtain ⟨N, hN⟩ := hQ.elim_directed_cover U hUo hUc hUd
  refine ⟨N.factorial, Nat.factorial_ne_zero N, fun x hx => ?_⟩
  have hmem := hN hx
  have hint : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E),
      IsDedekindDomain.HeightOneSpectrum.valuation E v ((N.factorial : E) * x) ≤ 1 := by
    intro v
    have h1 : algebraMap E (IsDedekindDomain.FiniteAdeleRing (𝓞 E) E) ((N.factorial : E) * x) ∈
        PI.AdCpctDenWork.intAd E := by
      rw [map_mul, map_natCast]
      exact hmem
    have h2 := (PI.AdCpctDenWork.mem_intAd _).1 h1 v
    rw [IsDedekindDomain.FiniteAdeleRing.algebraMap_apply,
      IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2
    exact h2
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one E _ hint
  exact ⟨r, by rw [NumberField.RingOfIntegers.coe_eq_algebraMap, hr]⟩

end GlobalTheory.CompanionTheory.AdeleDen
