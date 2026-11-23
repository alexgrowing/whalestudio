import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeLinearFormNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_linear_form_nonneg : ∀ (g : ℕ) (φs : InvFun ℤ) (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X], IsPolFan id g φs → Module.finrank ℤ X ≤ g → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCone id φs γ → ∃ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, ∀ be : LinearMap.BilinForm ℤ X, (∀ y z, be y z = be z y) → ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal be = ∑ i, c i • toReal (γ i) → 0 ≤ ℓ be ∧ (ℓ be : ℝ) = φs.evalZ be := by
  first | exact @GlobalTheory.PolFan.exists_intLinear_on_cone | exact GlobalTheory.PolFan.exists_intLinear_on_cone | (intros; apply GlobalTheory.PolFan.exists_intLinear_on_cone <;> assumption)
