import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousInvariantsNorms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_invariants_norms : ∀ (A A' : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A] [CommRing A'] [IsDomain A'] [Algebra A A'] [Module.Finite A A'], Function.Injective (algebraMap A A') → ∀ (σ J : Type) [Fintype σ] [Fintype J] (ℓ : J → σ → A'), ∃ (d : ℕ+) (n : ℕ) (B : Fin n → MvPolynomial σ A), (∀ i, (B i).IsHomogeneous d) ∧ ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] (x : A →+* C) (T : σ → C) (N : ℝ), (∀ x' : A' →+* C, x'.comp (algebraMap A A') = x → (⨆ j, ‖∑ s, x' (ℓ j s) * T s‖) = N) → N ^ (d : ℕ) = ⨆ i, ‖MvPolynomial.eval₂ x T (B i)‖ := by
  first | exact @GlobalTheory.NormFam.norm_of_family | exact GlobalTheory.NormFam.norm_of_family | (intros; apply GlobalTheory.NormFam.norm_of_family <;> assumption)
