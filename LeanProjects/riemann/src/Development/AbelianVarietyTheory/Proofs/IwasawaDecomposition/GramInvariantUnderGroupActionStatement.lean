import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramInvariantUnderGroupAction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_invariant_under_group_action : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp) (x : ToroidalCompactificationData s) (g₀ : GL (Fin N) D.host.E), g₀ ∈ (s.fd k).Γ → ∀ (f f' : (s.fd k).dom), f'.1 = ReciprocityTheory.ChartRestriction.G.FD.lact g₀ f.1 → ∀ t, x.gramW L k f' t = x.gramW L k f t ∧ x.gramOm L k f' t = x.gramOm L k f t := by
  first | exact @GlobalTheory.FrameGam.gram_lact | exact GlobalTheory.FrameGam.gram_lact | (intros; apply GlobalTheory.FrameGam.gram_lact <;> assumption)
