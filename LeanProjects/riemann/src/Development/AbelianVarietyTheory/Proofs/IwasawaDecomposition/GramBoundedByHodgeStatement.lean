import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramBoundedByHodge
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped Topology ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_bounded_by_hodge : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ y₀ : CxPts (genStr s.T.Z) σ, ∃ U ∈ 𝓝 y₀, ∃ (C : ℝ) (k : ℕ), ∀ y ∈ U, ¬ LiesIn y (genBd s.T.Z) → ∀ (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (τ : D.host.E →+* ℂ) (v : Fin (S.Dw.mult τ) → ℂ), (star v ⬝ᵥ x.gram y g τ *ᵥ v).re ≤ C * x.r σ y ^ k * (star v ⬝ᵥ (x.hodge σ).gram y g τ *ᵥ v).re ∧ (star v ⬝ᵥ (x.hodge σ).gram y g τ *ᵥ v).re ≤ C * x.r σ y ^ k * (star v ⬝ᵥ x.gram y g τ *ᵥ v).re := by
  first | exact @GlobalTheory.ShFam.MuLoc.hodge_comparison_near | exact GlobalTheory.ShFam.MuLoc.hodge_comparison_near | (intros; apply GlobalTheory.ShFam.MuLoc.hodge_comparison_near <;> assumption)
