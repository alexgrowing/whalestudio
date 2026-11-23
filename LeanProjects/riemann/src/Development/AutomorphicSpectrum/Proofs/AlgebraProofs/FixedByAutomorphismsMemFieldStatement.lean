import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FixedByAutomorphismsMemField
import Mathlib
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_by_automorphisms_mem_field : ∀ (F : IntermediateField ℚ ℂ) (c : ℂ), FiniteDimensional ℚ F → (∀ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) → g c = c) → c ∈ F := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.mem_of_fixed_aut | exact GlobalTheory.CompanionTheory.Ar.Flat.mem_of_fixed_aut | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.mem_of_fixed_aut <;> assumption)
