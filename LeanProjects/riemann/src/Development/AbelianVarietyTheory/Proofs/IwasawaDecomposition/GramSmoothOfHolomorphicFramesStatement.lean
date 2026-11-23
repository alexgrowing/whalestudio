import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_smooth_of_holomorphic_frames : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s) (m : ℕ) (B : Set (Fin m → ℂ)) (f : (Fin m → ℂ) → (s.fd k).dom), IsOpen B → (∀ τ a b, DifferentiableOn ℂ (fun v => ReciprocityTheory.ChartRestriction.G.FD.mat (f v).1 τ a b) B) → ∀ τ a b, ContDiffOn ℝ ∞ (fun v => x.gram (s.framePt k (f v)) (s.lieFrame k (f v)) τ a b) B := by
  first | exact @GlobalTheory.GramFamily.gram_smooth | exact GlobalTheory.GramFamily.gram_smooth | (intros; apply GlobalTheory.GramFamily.gram_smooth <;> assumption)
