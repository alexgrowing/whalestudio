import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MajorantHarnackHolomorphicHalfPlane
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorant_harnack_holomorphic_half_plane : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (x : ℂ → Frame X.Ψ N), DifferentiableOn ℂ x {w | T < w.im} → (∀ w : ℂ, T < w.im → x w ∈ X.dom) → ∀ w w' : ℂ, T < w.im → T < w'.im → ∀ (τ : X.Ψ) (v : Fin N → ℂ), X.maj (x w') τ v ≤ (2 + ‖w - w'‖ ^ 2 / ((w.im - T) * (w'.im - T))) * X.maj (x w) τ v := by
  first | exact @GlobalTheory.maj_harnack | exact GlobalTheory.maj_harnack | (intros; apply GlobalTheory.maj_harnack <;> assumption)
