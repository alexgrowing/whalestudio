import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FinMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.MaxIdem
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PrecompleteOfFinite
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locAbs :
    ∀ (Λ T : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [CommRing T] [Algebra Λ T] [Module.Finite Λ T] (ι : Type) (t : ι → T) (a : ι → Λ), Algebra.adjoin Λ (Set.range t) = ⊤ → ∃ e : T, IsIdempotentElem e ∧ (∀ i, ∃ n : ℕ, (t i - algebraMap Λ T (a i)) ^ n * e ∈ (maximalIdeal Λ).map (algebraMap Λ T)) ∧ 1 - e ∈ (maximalIdeal Λ).map (algebraMap Λ T) ⊔ Ideal.span (Set.range fun i => t i - algebraMap Λ T (a i)) ∧ (∀ s : T, ∃ c : Λ, s - algebraMap Λ T c ∈ (maximalIdeal Λ).map (algebraMap Λ T) ⊔ Ideal.span (Set.range fun i => t i - algebraMap Λ T (a i))) ∧ (e ≠ 0 → ((maximalIdeal Λ).map (algebraMap Λ T) ⊔ Ideal.span (Set.range fun i => t i - algebraMap Λ T (a i))).IsMaximal) :=
  _root_.UpperTheory.Reformulated.B.Qe2.locAbs
