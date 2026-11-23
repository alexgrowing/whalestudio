import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartDerivativeInjective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_derivative_injective : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (c : AlgChart (genStr s.T.Z) κ.σ₀ S.Dw.dim), ∀ z ∈ DomI D.what₂.Tau j (N - j), s.toCpt L k z ∈ c.e.source → Function.Injective (fderiv ℂ (fun v => c.e (s.toCpt L k (unflat v))) (flat z)) := by
  first | exact @GlobalTheory.ShFam.Imm.immersion | exact GlobalTheory.ShFam.Imm.immersion | (intros; apply GlobalTheory.ShFam.Imm.immersion <;> assumption)
