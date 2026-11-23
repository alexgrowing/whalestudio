import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeSmoothConj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_smooth_conj : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ σ' : κ.c.F →+* ℂ), σ = (starRingEnd ℂ).comp σ' → (x.hodge σ').SmoothOn (manifold s.T.Z σ') {y | ¬ LiesIn y (genBd s.T.Z)} → (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} := by
  first | exact @GlobalTheory.ShFam.HodgeConj.smoothOn_hodge_of_conj | exact GlobalTheory.ShFam.HodgeConj.smoothOn_hodge_of_conj | (intros; apply GlobalTheory.ShFam.HodgeConj.smoothOn_hodge_of_conj <;> assumption)
