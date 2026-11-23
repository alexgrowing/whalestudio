import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeConditionsProduct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_conditions_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X) (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ), (Fin m → LinearMap.BilinForm ℤ X) → Prop), (∀ (X₁ X₂ : Type) [AddCommGroup X₁] [Module (𝓞 E) X₁] [Module.Finite (𝓞 E) X₁] [AddCommGroup X₂] [Module (𝓞 E) X₂] [Module.Finite (𝓞 E) X₂] (f : X₁ ≃ₗ[𝓞 E] X₂) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X₂), Cn X₂ m γ → Cn X₁ m (fun i => pull f.toLinearMap (γ i))) → Z.j ≫ π = X.j → π ≫ X.s = Z.s → HasCones Cn X → HasCones Cn Z := by
  first | exact @GlobalTheory.TorRef.hasCones_of_map | exact GlobalTheory.TorRef.hasCones_of_map | (intros; apply GlobalTheory.TorRef.hasCones_of_map <;> assumption)
