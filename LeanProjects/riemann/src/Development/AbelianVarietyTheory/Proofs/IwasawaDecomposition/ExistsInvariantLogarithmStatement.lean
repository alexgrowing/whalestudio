import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantLogarithm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_logarithm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (R : Frame X.Ψ N → ℂ), DifferentiableOn ℂ R X.dom → (∀ x ∈ X.dom, R x ≠ 0) → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ N, R (rmul x b) = R x) → ∃ L : Frame X.Ψ N → ℂ, DifferentiableOn ℂ L X.dom ∧ (∀ x ∈ X.dom, Complex.exp (L x) = R x) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ N, L (rmul x b) = L x) := by
  first | exact @GlobalTheory.FrameLog.exists_invariant_log | exact GlobalTheory.FrameLog.exists_invariant_log | (intros; apply GlobalTheory.FrameLog.exists_invariant_log <;> assumption)
