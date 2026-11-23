import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcWitnessModelPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_witness_model_point : PartI → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (bF : c.F →+* ℂ) (_ : Algebra (FractionRing ℂ) ℂ) (_ : IsScalarTower ℂ (FractionRing ℂ) ℂ) (a : ArcIn D l (c.V W₀).subtype ℂ (bF.comp (c.V W₀).subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty), bF (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0 ∧ IsTypeFn H D.p D.q ty ∧ (∃ r z : c.V W₀, (((c.V W₀).subtype r : c.F) : ℂ) = H.rt0 ∧ (((c.V W₀).subtype z : c.F) : ℂ) = zeta l.A) ∧ χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (bF.comp (c.V W₀).subtype) ∧ (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) ∧ (∀ x : Sp (PowerSeries ℂ), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧ Nontrivial W.P.D.toPre.X ∧ 0 < Fu.n := by
  first | exact @GlobalTheory.ArcWitness.exists_arcWit | exact GlobalTheory.ArcWitness.exists_arcWit | (intros; apply GlobalTheory.ArcWitness.exists_arcWit <;> assumption)
