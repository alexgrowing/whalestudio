import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAevalValuationDvr
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_aeval_valuation_dvr : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)],
    Function.Injective (algebraMap T V) →
    ∀ (γ : V) (ϖ u : T) (k : ℕ), Irreducible ϖ → IsUnit u → IsUnit (k : T) → 0 < k →
    γ ^ k = algebraMap T V u →
    ∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h' := by
  first | (exact @GlobalTheory.kummer_valuation) | (exact GlobalTheory.kummer_valuation) | (intros; apply GlobalTheory.kummer_valuation  <;> assumption)
