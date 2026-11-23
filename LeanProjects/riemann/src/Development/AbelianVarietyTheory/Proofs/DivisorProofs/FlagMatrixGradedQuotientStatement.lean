import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixGradedQuotient
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_matrix_graded_quotient : ∀ (B Y : Scheme.{0}) (M : B.Modules) (r : ℕ) (hM : IsVB M r) (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (V : B.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (K : Type) [Field K] (y : Sp K ⟶ Y) (A : Matrix (Fin r) (Fin r) K), FlagMat hM π fl hf y A → ∀ (i : Fin r) (ch : Chart (fl.gr i) 1) (W : Y.Opens) (hW : W ≤ ch.U) (hWV : W ≤ π ⁻¹ᵁ V) (t : Γ(fl.F i.succ, W)), (fl.π i).app W t = Twist.resM _ hW (ch.e 0) → ∀ (hy : ⊤ ≤ y ⁻¹ᵁ W) (cf : Fin r → K), coordAt hM π hf y hWV hy ((fl.ι i.succ).app W t) = Matrix.vecMul cf A → cf i ≠ 0 := by
  first | exact @GlobalTheory.FlagCls.FlagMat.coeff_ne_zero | exact GlobalTheory.FlagCls.FlagMat.coeff_ne_zero | (intros; apply GlobalTheory.FlagCls.FlagMat.coeff_ne_zero <;> assumption)
