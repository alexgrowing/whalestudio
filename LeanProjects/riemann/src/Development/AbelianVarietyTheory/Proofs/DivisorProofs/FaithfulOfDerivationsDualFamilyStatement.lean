import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfulOfDerivationsDualFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceRep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.faithful_of_derivations_dualFamily : ∀ (U A ι : Type) [Ring U] [Algebra ℂ U] [CommRing A] [Algebra ℂ A] [Fintype ι] [DecidableEq ι] (e : ι → U), Algebra.adjoin ℂ (Set.range e) = ⊤ → (∀ a b, e a * e b - e b * e a ∈ Submodule.span ℂ (Set.range e)) → ∀ (π : U →ₐ[ℂ] Module.End ℂ A), (∀ k (x y : A), π (e k) (x * y) = π (e k) x * y + x * π (e k) y) → ∀ (χ : A →ₐ[ℂ] ℂ) (a : ι → A), (∀ k, χ (a k) = 0) → (∀ i k, χ (π (e i) (a k)) = if i = k then 1 else 0) → ∀ u : U, (∀ x : A, χ (π u x) = 0) → u = 0 := by
  first | exact @GlobalTheory.faithful_of_derivations_dual_family | exact GlobalTheory.faithful_of_derivations_dual_family | (intros; apply GlobalTheory.faithful_of_derivations_dual_family <;> assumption)
