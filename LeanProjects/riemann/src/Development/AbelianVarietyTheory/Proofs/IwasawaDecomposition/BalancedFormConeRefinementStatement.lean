import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedFormConeRefinement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.balanced_form_cone_refinement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (k : ℕ) (γ : Fin k → LinearMap.BilinForm ℤ X), Module.finrank ℚ E * q ≤ g → IsPolFan id g φs → Refines H q φs 𝒩 φ → Module.finrank (𝓞 E) X ≤ q → ConeZ E φs X k γ → ∀ be ∈ balForms H.bar X, (∀ y, 0 ≤ be y y) → GlobalTheory.ChartMono.InRealCone γ be → ∃ (k₁ : ℕ) (δ : Fin k₁ → LinearMap.BilinForm ℤ X), IsCone H.bar φ δ ∧ GlobalTheory.ChartMono.InRealCone δ be ∧ ∀ β ∈ balForms H.bar X, GlobalTheory.ChartMono.InRealCone γ β → ∃ (M : ℕ) (a : Fin k₁ → ℤ), 0 < M ∧ (M : ℤ) • β = ∑ i, a i • δ i := by
  first | exact @GlobalTheory.PolFan.FullCone.exists_cone_span_balanced | exact GlobalTheory.PolFan.FullCone.exists_cone_span_balanced | (intros; apply GlobalTheory.PolFan.FullCone.exists_cone_span_balanced <;> assumption)
