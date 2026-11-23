import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ZariskiNoetherianInduction

open TopologicalSpace PrimeSpectrum

theorem UpperTheory.Et.noethSp :
    ∀ (k : Type) [Field k] (n : ℕ) (P : Set (Fin n → k) → Prop), P ∅ → (∀ s t, s ⊆ t → P t → P s) → (∀ s t, P s → P t → P (s ∪ t)) → (∀ I : Ideal (MvPolynomial (Fin n) k), I.IsPrime → ∃ g, g ∉ I ∧ P ({c | ∀ p ∈ I, MvPolynomial.eval c p = 0} ∩ {c | MvPolynomial.eval c g ≠ 0})) → P Set.univ :=
  _root_.UpperTheory.Reformulated.B.ZariskiNoetherianInduction.noetherian_induction_zariski
