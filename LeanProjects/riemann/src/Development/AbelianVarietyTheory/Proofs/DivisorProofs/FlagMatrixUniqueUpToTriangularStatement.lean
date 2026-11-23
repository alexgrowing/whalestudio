import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixUniqueUpToTriangular
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_matrix_unique_up_to_triangular : ∀ (B Y : Scheme.{0}) (M : B.Modules) (r : ℕ) (hM : IsVB M r) (π : Y ⟶ B) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (V : B.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (K : Type) [CommRing K] [IsLocalRing K] (y : Sp K ⟶ Y), ⊤ ≤ (y ≫ π) ⁻¹ᵁ V → (∃ A, FlagMat hM π fl hf y A) ∧ (∀ A A', FlagMat hM π fl hf y A → FlagMat hM π fl hf y A' → ∃ T : Matrix (Fin r) (Fin r) K, IsUnit T.det ∧ (∀ i j, i < j → T i j = 0) ∧ A' = T * A) ∧ ∀ (K' : Type) [CommRing K'] (ψ : K →+* K') (A : Matrix (Fin r) (Fin r) K), FlagMat hM π fl hf y A → FlagMat hM π fl hf (spMap ψ ≫ y) (A.map ψ) := by
  first | exact @GlobalTheory.FlagCls.flagMat_local | exact GlobalTheory.FlagCls.flagMat_local | (intros; apply GlobalTheory.FlagCls.flagMat_local <;> assumption)
