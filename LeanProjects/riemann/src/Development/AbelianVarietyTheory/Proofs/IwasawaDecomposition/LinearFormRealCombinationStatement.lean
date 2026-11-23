import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearFormRealCombination
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_form_real_combination : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (c : Fin m → ℝ) (be : LinearMap.BilinForm ℤ X),
    GlobalTheory.PolFan.toReal be = ∑ i, c i • GlobalTheory.PolFan.toReal (γ i) → ((ℓ be : ℤ) : ℝ) = ∑ i, c i * (ℓ (γ i) : ℝ) := by
  first | exact @GlobalTheory.PolFanReal.linearForm_of_toReal_eq | exact GlobalTheory.PolFanReal.linearForm_of_toReal_eq | (intros; apply GlobalTheory.PolFanReal.linearForm_of_toReal_eq <;> assumption)
