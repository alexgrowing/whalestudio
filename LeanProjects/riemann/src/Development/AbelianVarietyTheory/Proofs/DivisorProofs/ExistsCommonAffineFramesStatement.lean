import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonAffineFrames
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCoordMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_affine_frames' : ∀ (X : Scheme.{0}) (M M' : X.Modules) (r : ℕ), IsVB M r → IsVB M' r → ∀ x : X, ∃ (V : X.Opens)
    (f : Fin r → Γ(M, V)) (f' : Fin r → Γ(M', V)), VB.IsFrame f ∧ VB.IsFrame f' ∧ IsAffineOpen V ∧ x ∈ V := by
  first | exact @GlobalTheory.CommonFrames.exists_common_affine_frames | exact GlobalTheory.CommonFrames.exists_common_affine_frames | (intros; apply GlobalTheory.CommonFrames.exists_common_affine_frames <;> assumption)
