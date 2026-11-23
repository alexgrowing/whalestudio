import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetValueTangentCombinationSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_value_tangent_combination_smul : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (m : ℕ) (v : Fin m → (epsR R ⟶ G)) (x : Fin m → R) (a : R) (k : ℕ) (U : G.left.Opens) (f : Γ(G.left, U)), jetVal (tanComb (a • x) v) k U f = a ^ k * jetVal (tanComb x v) k U f := by
  first | exact @GlobalTheory.SecJet.jetVal_tanComb_smul | exact GlobalTheory.SecJet.jetVal_tanComb_smul | (intros; apply GlobalTheory.SecJet.jetVal_tanComb_smul <;> assumption)
