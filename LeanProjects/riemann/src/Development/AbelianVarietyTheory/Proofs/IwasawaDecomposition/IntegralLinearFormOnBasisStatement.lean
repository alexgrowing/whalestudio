import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralLinearFormOnBasis
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_linear_form_on_basis : ∀ {O : Type} [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite ℤ X] (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (hγ : ∀ i, γ i ∈ GlobalTheory.PolFan.balForms bar X),
    GlobalTheory.Toroidal.IsPartOfBasis (fun i => (⟨γ i, hγ i⟩ : GlobalTheory.PolFan.balForms bar X)) →
    ∀ w : Fin m → ℤ, ∃ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, ∀ i, ℓ (γ i) = w i := by
  first | exact @GlobalTheory.BalExt.exists_linearForm_ext | exact GlobalTheory.BalExt.exists_linearForm_ext | (intros; apply GlobalTheory.BalExt.exists_linearForm_ext <;> assumption)
