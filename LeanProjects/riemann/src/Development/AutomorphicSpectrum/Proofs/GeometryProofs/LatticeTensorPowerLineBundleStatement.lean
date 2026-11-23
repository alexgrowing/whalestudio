import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerLineBundle
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_tensor_power_line_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)), (∀ i, (Λ i).IsVBOn T 1 ⊤) → ∀ a : I → ℤ, (Lat.tens Λ a).IsVBOn T 1 ⊤ ∧ ∀ p ∈ T, ∀ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) → (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LatTens.tens_isVBOn | exact GlobalTheory.CompanionTheory.Ar.LatTens.tens_isVBOn | (intros; apply GlobalTheory.CompanionTheory.Ar.LatTens.tens_isVBOn <;> assumption)
