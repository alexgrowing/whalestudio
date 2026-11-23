import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramTransformOfCoordinateChange
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_transform_of_coordinate_change : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s) (f f' : (s.fd k).dom), s.zOf L k f = s.zOf L k f' → ∀ t, (∀ T, coW (s.fd k) s.j_le f'.1 (s.lab L k t) * T = coW (s.fd k) s.j_le f.1 (s.lab L k t) → x.gramW L k f t = Tᴴ * x.gramW L k f' t * T) ∧ ∀ T, coOm (s.fd k) s.j_le f'.1 (s.lab L k t) * T = coOm (s.fd k) s.j_le f.1 (s.lab L k t) → x.gramOm L k f t = Tᴴ * x.gramOm L k f' t * T := by
  first | exact @GlobalTheory.FramePairGram.gram_frames_eq | exact GlobalTheory.FramePairGram.gram_frames_eq | (intros; apply GlobalTheory.FramePairGram.gram_frames_eq <;> assumption)
