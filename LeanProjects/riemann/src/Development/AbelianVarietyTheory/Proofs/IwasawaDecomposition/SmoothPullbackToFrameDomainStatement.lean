import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothPullbackToFrameDomain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_pullback_to_frame_domain : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (W : Set (CxPts (genStr s.T.Z) κ.σ₀)) (φ : CxPts (genStr s.T.Z) κ.σ₀ → ℝ), IsOpen W → (manifold s.T.Z κ.σ₀).SmoothOn W φ → IsOpen {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ W} ∧ ContDiffOn ℝ ∞ (fun v => φ (s.toCpt L k (unflat v))) {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ W} ∧ ∀ (c : AlgChart (genStr s.T.Z) κ.σ₀ S.Dw.dim), ∀ z ∈ DomI D.what₂.Tau j (N - j), s.toCpt L k z ∈ W → s.toCpt L k z ∈ c.e.source → ∀ ξ, ddc (φ ∘ s.toCpt L k) z ξ = ddcForm φ c (s.toCpt L k z) (fderiv ℂ (fun v => c.e (s.toCpt L k (unflat v))) (flat z) (flat ξ)).ofLp := by
  first | exact @GlobalTheory.ShFam.smoothOn_toCpt_ddc | exact GlobalTheory.ShFam.smoothOn_toCpt_ddc | (intros; apply GlobalTheory.ShFam.smoothOn_toCpt_ddc <;> assumption)
