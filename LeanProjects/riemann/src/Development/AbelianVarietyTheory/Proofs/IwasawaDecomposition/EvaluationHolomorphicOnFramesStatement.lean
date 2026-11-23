import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationHolomorphicOnFrames
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_holomorphic_on_frames : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (U : (gen s.T.Z).Opens) (f : Γ(gen s.T.Z, U)), IsOpen {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ ptsIn (genStr s.T.Z) κ.σ₀ U} ∧ DifferentiableOn ℂ (fun v => ev (genStr s.T.Z) κ.σ₀ U f (s.toCpt L k (unflat v))) {v ∈ DomFlat D.what₂.Tau j (N - j) | s.toCpt L k (unflat v) ∈ ptsIn (genStr s.T.Z) κ.σ₀ U} := by
  first | exact @GlobalTheory.ShFam.isHol_toCpt | exact GlobalTheory.ShFam.isHol_toCpt | (intros; apply GlobalTheory.ShFam.isHol_toCpt <;> assumption)
