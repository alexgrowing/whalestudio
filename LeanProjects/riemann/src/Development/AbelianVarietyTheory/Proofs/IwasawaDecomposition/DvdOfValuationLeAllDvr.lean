import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory

theorem dvd_of_forall_complete_dvr_order_le :
    ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R →
    ∀ r s : R, r ≠ 0 →
    (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ f : R →+* W,
      Function.Injective f → ∀ n m : ℕ, Associated (f r) (ϖ ^ n) → Associated (f s) (ϖ ^ m) → n ≤ m) → r ∣ s := by
  intro R _ _ _ _ _ r s hr H
  by_cases hs : s = 0
  · exact hs ▸ dvd_zero r
  refine dvd_of_forall_height_eq_one hr fun p _ hp hrp => ?_
  have hp0 : p ≠ ⊥ := p.ne_bot_of_height_eq_one hp
  obtain ⟨O, _, _, hdvr, hcpl, φ, hker, hcomap⟩ :=
    exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal R) p (bot_lt_iff_ne_bot.2 hp0)
  have hinj : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).2 hker
  have hch : CharZero O := (RingHom.charZero_iff hinj).1 inferInstance
  have hC : CDvr O := ⟨hdvr, hcpl, hch⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  haveI : IsDiscreteValuationRing (Localization.AtPrime p) :=
    isDiscreteValuationRing_of_height_eq_one p hp (Localization.AtPrime p)
  have hinjB : Function.Injective (algebraMap R (Localization.AtPrime p)) :=
    IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  obtain ⟨c, hc'⟩ := ValuationRing.cond (algebraMap R (Localization.AtPrime p) r)
    (algebraMap R (Localization.AtPrime p) s)
  obtain ⟨⟨x, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl c
  rcases hc' with h | h
  · refine ⟨t, t.2, x, ?_⟩
    apply hinjB
    have h2 := congrArg (· * algebraMap R (Localization.AtPrime p) t) h
    simp only at h2
    rw [mul_assoc, IsLocalization.mk'_spec] at h2
    rw [map_mul, map_mul, mul_comm, ← h2]
  · have e : s * x = r * t := by
      apply hinjB
      have h2 := congrArg (· * algebraMap R (Localization.AtPrime p) t) h
      simp only at h2
      rw [mul_assoc, IsLocalization.mk'_spec] at h2
      rw [map_mul, map_mul, h2]
    by_cases hx : x ∈ p
    · exfalso
      have ht0 : (t : R) ≠ 0 := fun h0 => t.2 (h0 ▸ p.zero_mem)
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [mul_zero] at e
        exact mul_ne_zero hr ht0 e.symm
      have hmem : ∀ y : R, φ y ∈ maximalIdeal O ↔ y ∈ p := fun y => by
        rw [← Ideal.mem_comap, hcomap]
      have hφx : φ x ∈ maximalIdeal O := (hmem x).2 hx
      have hφt : IsUnit (φ t) := by
        by_contra hu
        exact t.2 ((hmem t).1 ((mem_maximalIdeal _).2 hu))
      have hφs : φ s ≠ 0 := fun h0 => hs (hinj (h0.trans (map_zero φ).symm))
      have hφx0 : φ x ≠ 0 := fun h0 => hx0 (hinj (h0.trans (map_zero φ).symm))
      obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hφs hϖ
      obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hφx0 hϖ
      have hk1 : k ≠ 0 := by
        rintro rfl
        exact (mem_maximalIdeal _).1 hφx (hk.isUnit_iff.2 (by simp))
      have h1 : φ r * φ t = φ s * φ x := by rw [← map_mul, ← map_mul, e]
      have hr' : Associated (φ r) (ϖ ^ (m + k)) := by
        have h3 : Associated (φ r) (φ s * φ x) := by
          rw [← h1]; exact associated_mul_unit_right _ _ hφt
        rw [pow_add]
        exact h3.trans (hm.mul_mul hk)
      have := H O hC ϖ hϖ φ hinj (m + k) m hr' hm
      omega
    · exact ⟨x, hx, t, by rw [mul_comm x s, e]⟩

end GlobalTheory
