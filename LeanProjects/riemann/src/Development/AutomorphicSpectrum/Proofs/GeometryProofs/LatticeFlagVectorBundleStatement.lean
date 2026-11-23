import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFlagVectorBundle
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_flag_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (g r : ℕ) (W : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ → (∀ k, b₀ k ∈ W) → L.IsVBOn T g W → (∀ n : ℕ, ∃ s W', (L.map (flagStep Ω b₀ n).mkQ).IsVBOn T s W') → (L.inter (Submodule.span Ω (Set.range b₀))).IsFlagVBOn T b₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isFlagVBOn_inter_of_steps | exact GlobalTheory.CompanionTheory.Ar.isFlagVBOn_inter_of_steps | (intros; apply GlobalTheory.CompanionTheory.Ar.isFlagVBOn_inter_of_steps <;> assumption)
