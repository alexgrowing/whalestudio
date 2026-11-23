import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixOfAdaptedCoordinates
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_matrix_of_adapted_coordinates : ∀ (B Y : Scheme.{0}) (M : B.Modules) (r : ℕ) (hM : IsVB M r) (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (V : B.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (K : Type) [CommRing K] (y : Sp K ⟶ Y) (W : Y.Opens) (hWV : W ≤ π ⁻¹ᵁ V) (hy : ⊤ ≤ y ⁻¹ᵁ W) (s : Fin r → Γ((Scheme.Modules.pullback π).obj M, W)), Adapted fl s → FlagMat hM π fl hf y (Matrix.of fun i => coordAt hM π hf y hWV hy (s i)) := by
  first | exact @GlobalTheory.FlagCls.AdaptMat.flagMat_of_adapted | exact GlobalTheory.FlagCls.AdaptMat.flagMat_of_adapted | (intros; apply GlobalTheory.FlagCls.AdaptMat.flagMat_of_adapted <;> assumption)
