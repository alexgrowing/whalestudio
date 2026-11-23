import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixTransportFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_matrix_transport_fibre : ∀ (B Y : Scheme.{0}) (M : B.Modules) (r : ℕ) (hM : IsVB M r) (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (V : B.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (K : Type) [Field K] (x : Sp K ⟶ B), ⊤ ≤ x ⁻¹ᵁ V → ∀ (fl' : Vert.Flag ((Scheme.Modules.pullback x).obj M) r) (A : Matrix (Fin r) (Fin r) K), FlagMat hM x fl' hf (𝟙 (Sp K)) A → ∀ (y : Sp K ⟶ Y) (w : y ≫ π = x), FlagMat hM π fl hf y A → StepIso π fl fl' y w := by
  first | exact @GlobalTheory.FlagCls.stepIso_of_flagMat | exact GlobalTheory.FlagCls.stepIso_of_flagMat | (intros; apply GlobalTheory.FlagCls.stepIso_of_flagMat <;> assumption)
