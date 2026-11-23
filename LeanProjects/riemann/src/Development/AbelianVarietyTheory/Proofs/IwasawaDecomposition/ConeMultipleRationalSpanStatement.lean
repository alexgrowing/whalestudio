import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMultipleRationalSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_multiple_rational_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (k : ℕ) (δ : Fin k → LinearMap.BilinForm ℤ X) (N : ℕ) (S : Set (LinearMap.BilinForm ℤ X)), IsPolFanOn H.bar φ X → IsCone H.bar φ δ → (∀ β ∈ S, ∃ (M : ℕ) (a : Fin k → ℤ), 0 < M ∧ (M : ℤ) • β = ∑ i, a i • δ i) → ∀ be : LinearMap.BilinForm ℤ X, GlobalTheory.ChartMono.InRealCone δ be → ∃ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (ℓ be : ℝ) = N * φ.evalZ be ∧ ∀ β ∈ S, β ∈ balForms H.bar X → (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β := by
  first | exact @GlobalTheory.ChartMono.exists_intPiece | exact GlobalTheory.ChartMono.exists_intPiece | (intros; apply GlobalTheory.ChartMono.exists_intPiece <;> assumption)
