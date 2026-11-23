import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricPullbackGramAndInvariance
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.metric_pullback_gram_and_invariance : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s), (∀ (f : (s.fd k).dom) t, (coW (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * x.metW L k (s.zOf L k f) t * coW (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramW L k f t ∧ (coOm (s.fd k) s.j_le f.1 (s.lab L k t))ᴴ * x.metOm L k (s.zOf L k f) t * coOm (s.fd k) s.j_le f.1 (s.lab L k t) = x.gramOm L k f t) ∧ ∀ g ∈ gammaU (s.fd k) s.j_le (s.lab L k), ∀ z ∈ DomI D.what₂.Tau j (N - j), ∀ t, (jW (g t) (z t))ᴴ * x.metW L k (moebI g z) t * jW (g t) (z t) = x.metW L k z t ∧ (kapQ (g t) (z t))ᴴ * x.metOm L k (moebI g z) t * kapQ (g t) (z t) = x.metOm L k z t := by
  first | exact @GlobalTheory.ShFam.MetLaws.metLaws | exact GlobalTheory.ShFam.MetLaws.metLaws | (intros; apply GlobalTheory.ShFam.MetLaws.metLaws <;> assumption)
