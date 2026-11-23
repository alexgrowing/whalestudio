import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixChangeOfFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_matrix_change_of_frame : ∀ (B Y : Scheme.{0}) (M : B.Modules) (r : ℕ) (hM : IsVB M r) (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (V : B.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (V' : B.Opens) (f' : Fin r → Γ(M, V')) (hf' : IsFrame f') (K : Type) [CommRing K] (y : Sp K ⟶ Y) (x : Sp K ⟶ B) (hxx : ⊤ ≤ x ⁻¹ᵁ (V ⊓ V')) (A : Matrix (Fin r) (Fin r) K), y ≫ π = x → FlagMat hM π fl hf' y A → IsUnit (Matrix.of fun a b => TangentOrigin.evalPt x (V ⊓ V') hxx (trCo hf f' b a)).det ∧ FlagMat hM π fl hf y (A * Matrix.of fun a b => TangentOrigin.evalPt x (V ⊓ V') hxx (trCo hf f' b a)) := by
  first | exact @GlobalTheory.FlagCls.flagMat_change_frame | exact GlobalTheory.FlagCls.flagMat_change_frame | (intros; apply GlobalTheory.FlagCls.flagMat_change_frame <;> assumption)
