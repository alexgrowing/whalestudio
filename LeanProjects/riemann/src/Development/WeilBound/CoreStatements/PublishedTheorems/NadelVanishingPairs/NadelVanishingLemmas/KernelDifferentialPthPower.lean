import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsDerivationNonPthPower

open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem dK_eq_zero_imp_pow : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (f : K),
    dK f = 0 → ∃ g : K, f = g ^ p := by
  intro K _ p _ _ f hf
  by_contra hne
  push_neg at hne
  obtain ⟨D, hD⟩ := DerivExt.exists_derivation p f hne
  have h := D.liftKaehlerDifferential_comp_D f
  have h0 : (KaehlerDifferential.D ℤ K) f = 0 := hf
  rw [h0, map_zero, hD] at h
  exact zero_ne_one h

end GlobalTheory
