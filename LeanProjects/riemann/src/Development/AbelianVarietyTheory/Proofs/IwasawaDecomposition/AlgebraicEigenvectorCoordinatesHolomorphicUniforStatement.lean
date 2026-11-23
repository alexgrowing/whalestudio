import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicEigenvectorCoordinatesHolomorphicUnifor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqOfConjEqOne
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts
open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_eigenvector_coordinates_holomorphic_uniformisation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (d : ℕ) (u₀ : V d) (R : Type) [CommRing R] (φR : c.F →+* R) (xR : Sp R ⟶ Z.X) (fR : EigFrame Z φR xR) (ev : V d → (R →+* ℂ)) (k : U.Comp) (G : V d → ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q)) (τ : E →+* ℂ), (∀ t, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ev u t) u) → (∀ τ' a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => ReciprocityTheory.ChartRestriction.G.FD.mat (G u) τ' a b) u) → (∀ᶠ u in 𝓝 u₀, (ev u).comp φR = σ) → (∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, (cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z = spMap (ev u) ≫ xR) → ∃ M : V d → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ, (∀ a b, ∀ᶠ u in 𝓝 u₀, DifferentiableAt ℂ (fun u => M u a b) u) ∧ ∀ᶠ u in 𝓝 u₀, ∃ h : G u ∈ (U.X k).dom, ∀ i, IsCombAtG Z.t ((cxPt Z (U.un k ⟨G u, h⟩)).1 ≫ genι Z) ((cxFrame Z (U.un k ⟨G u, h⟩)).v τ) (fun b => M u b i) (spMap (dualMap (ev u)) ≫ fR.v τ i) := by
  first | exact @GlobalTheory.HolCoordEv.coords_holomorphic | exact GlobalTheory.HolCoordEv.coords_holomorphic | (intros; apply GlobalTheory.HolCoordEv.coords_holomorphic <;> assumption)
