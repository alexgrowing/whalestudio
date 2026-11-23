import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameDomainCoordinatesHolomorphic
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_domain_coordinates_holomorphic : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp), ∃ f : Pt D.what₂.Tau j (N - j) → (s.fd k).dom, (∀ z ∈ DomI D.what₂.Tau j (N - j), s.zOf L k (f z) = z ∧ ∀ τ, coW (s.fd k) s.j_le (f z).1 τ = 1 ∧ coOm (s.fd k) s.j_le (f z).1 τ = 1) ∧ ∀ τ a b, DifferentiableOn ℂ (fun v => ReciprocityTheory.ChartRestriction.G.FD.mat (f (unflat v)).1 τ a b) (DomFlat D.what₂.Tau j (N - j)) := by
  first | exact @GlobalTheory.ShFam.exists_holo_frame | exact GlobalTheory.ShFam.exists_holo_frame | (intros; apply GlobalTheory.ShFam.exists_holo_frame <;> assumption)
