import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorOfDualPointAdditiveLieComb
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentVectorOfDualPoint_additive_lieComb : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) [Algebra (FractionRing R) ℂ] (N : NumD ℂ) (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (n : ℕ) (c : Fin n → R) (v : Fin n → (epsR R ⟶ D.P.A)) (w : epsR R ⟶ D.P.A) (W : Fin n → Fin g → ℂ) (b : Fin n → (TE R ℂ ⟶ D.P.A)) (bw : TE R ℂ ⟶ D.P.A), (∀ j, IsTangent (v j)) → IsLieComb c v w → (∀ j, (b j).left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (v j).left) → bw.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ w.left → (∀ j, IsD ν d (W j) (b j)) → IsD ν d (∑ j, (algebraMap (FractionRing R) ℂ) (algebraMap R (FractionRing R) (c j)) • W j) bw := by
  first | exact @GlobalTheory.isD_lieComb | exact GlobalTheory.isD_lieComb | (intros; apply GlobalTheory.isD_lieComb <;> assumption)
