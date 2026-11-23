import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryModuliFinitePointsWithGivenPolarisedFibre
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryModuli_finite_points_with_given_polarisedFibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (s₀ : Sp K ⟶ Sp (KA l)), Set.Finite {x : Sp K ⟶ Xo.X | x ≫ Xo.s = s₀ ∧ ∃ α : P.A.left ⟶ Xo.univ.t.G.left, IsGrpPullback P.A Xo.univ.t.G x α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α)} := by
  first | exact @GlobalTheory.UMinQF.finite_points | exact GlobalTheory.UMinQF.finite_points | (intros; apply GlobalTheory.UMinQF.finite_points <;> assumption)
