import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualFamilyIsBasis
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_family_is_basis : ∀ (V : Type) [CommRing V] (L : Type) [AddCommGroup L] [Module V L] (n : ℕ) (b : Module.Basis (Fin n) V L) (u : Fin n → L) (f : Fin n → (L →ₗ[V] V)) (N : V), IsUnit N → (∀ i j, f j (u i) = if i = j then N else 0) → LinearIndependent V u ∧ Submodule.span V (Set.range u) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit | exact GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit | (intros; apply GlobalTheory.CompanionTheory.CommAlg.linearIndependent_span_of_dual_unit <;> assumption)
