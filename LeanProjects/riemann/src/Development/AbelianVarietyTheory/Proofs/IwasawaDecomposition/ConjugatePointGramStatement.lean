import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugatePointGram
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped Topology ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_point_gram : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), ¬ Formalism.L2.PjFree.GoodEmb κ.c σ → ∀ y : CxPts (genStr s.T.Z) σ, ∃ y' : CxPts (genStr s.T.Z) ((starRingEnd ℂ).comp σ), (LiesIn y' (genBd s.T.Z) ↔ LiesIn y (genBd s.T.Z)) ∧ x.r _ y' = x.r σ y ∧ ∀ g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z), ∃ g' : EigFrame s.T.Z ((starRingEnd ℂ).comp σ) (y'.1 ≫ genι s.T.Z), ∀ τ : D.host.E →+* ℂ, x.gram y' g' τ = (x.gram y g τ).map (starRingEnd ℂ) ∧ (x.hodge _).gram y' g' τ = ((x.hodge σ).gram y g τ).map (starRingEnd ℂ) := by
  first | exact @GlobalTheory.ShFam.hodge_gram_conjPt | exact GlobalTheory.ShFam.hodge_gram_conjPt | (intros; apply GlobalTheory.ShFam.hodge_gram_conjPt <;> assumption)
