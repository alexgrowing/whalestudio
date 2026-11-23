import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarHermitianFormLineFrameBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dbar_hermitian_form_line_frame_bound : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (S : ShortComplex X.Modules) (h : Met p σ S.X₂ (1 + 1)) (hS : S.ShortExact) (h₁ : IsVB S.X₁ 1) (h₃ : IsVB S.X₃ 1), h.IsCInf → ∀ (U : X.Opens) (t : Γ(S.X₁, U)) (w : Γ(S.X₂, U)), IsFrame (fun _ : Fin 1 => t) → ∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source, y ∈ ptsIn p σ U → ∀ ξ : V D, ‖dbar (fun v => h.form w (S.f.app U t) (c.e.symm v)) (c.e y) ξ - h.form w (S.f.app U t) y * dbar (fun v => (Real.log (h.form (S.f.app U t) (S.f.app U t) (c.e.symm v)).re : ℂ)) (c.e y) ξ‖ ^ 2 = ((h.form (S.f.app U t) (S.f.app U t) y).re * (h.form w w y).re - ‖h.form w (S.f.app U t) y‖ ^ 2) * (∑ j, ∑ l, ξ j * bcMat h hS h₁ h₃ c y j l * starRingEnd ℂ (ξ l)).re := by
  first | exact @GlobalTheory.MixDens.norm_dbar_projection_sq_bcMat | exact GlobalTheory.MixDens.norm_dbar_projection_sq_bcMat | (intros; apply GlobalTheory.MixDens.norm_dbar_projection_sq_bcMat <;> assumption)
