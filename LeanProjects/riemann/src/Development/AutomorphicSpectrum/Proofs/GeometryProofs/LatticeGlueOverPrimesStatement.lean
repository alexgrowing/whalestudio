import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeGlueOverPrimes
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_glue_over_primes : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] [CharZero Ω] [IsLocallyNoetherian X] (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) (r : ℕ) (V : Submodule Ω E), IsCptGen ξ → (∀ l ∈ S, l.Prime) → L₀.IsVBOn {q | ∀ l ∈ S, ¬ InFibre ξ l q} r V → (∀ l ∈ S, (Lp l).IsVBOn {q | ∀ l' : ℕ, l'.Prime → l' ≠ l → ¬ InFibre ξ l' q} r V) → (∀ l ∈ S, ∀ q : Cpt ξ, (∀ l' : ℕ, l'.Prime → ¬ InFibre ξ l' q) → Lp l q = L₀ q) → ∃ L : Lat ξ E, L.IsVB r V ∧ (∀ q : Cpt ξ, (∀ l ∈ S, ¬ InFibre ξ l q) → L q = L₀ q) ∧ ∀ l ∈ S, ∀ q : Cpt ξ, InFibre ξ l q → L q = Lp l q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.lat_glue | exact GlobalTheory.CompanionTheory.Ar.lat_glue | (intros; apply GlobalTheory.CompanionTheory.Ar.lat_glue <;> assumption)
