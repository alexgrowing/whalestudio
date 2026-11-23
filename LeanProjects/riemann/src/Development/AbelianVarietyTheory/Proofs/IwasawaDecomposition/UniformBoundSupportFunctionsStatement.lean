import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformBoundSupportFunctions
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_bound_support_functions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], IsPolFanOn H.bar φ X → ∀ Nmax : ℕ, (∀ (m : ℕ) (ε : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ ε → ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧ N ≤ Nmax ∧ (∀ i, (ℓ (ε i) : ℝ) = N * φ.evalZ (ε i)) ∧ (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β) ∧ ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β = ℓ β → ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • ε i) → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ δ → ∀ w ∈ balForms H.bar X, (∀ y, 0 ≤ w y y) → ∃ (m' : ℕ) (ε : Fin m' → LinearMap.BilinForm ℤ X), IsCone H.bar φ ε ∧ (∀ j, ∃ (k : ℕ) (c : Fin m' → ℕ), 0 < k ∧ k • δ j = ∑ i, c i • ε i) ∧ ∃ (k : ℕ) (c : Fin m' → ℤ), 0 < k ∧ (k : ℤ) • w = ∑ i, c i • ε i := by
  first | exact @GlobalTheory.ConeGrow.exists_cone_of_large_multiple | exact GlobalTheory.ConeGrow.exists_cone_of_large_multiple | (intros; apply GlobalTheory.ConeGrow.exists_cone_of_large_multiple <;> assumption)
