import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearUniformisationOfCompleteDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearUniformisation_of_complete_dvr : (AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.LG = s.P.L ∧ U.gen = s.gen ∧ HEq U.cubG s.P.c) → Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (t : SAB H (Sp V)) (A : PolAV (Sp (FractionRing V))) (gen : (Over.pullback (jK V)).obj t.G ≅ A.A), IsMonHom gen.hom → (∃ w : LB.Iso (A.L.pull gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK V))), w.IsGen) → (∃ S : SplitExt (Sp (IsLocalRing.ResidueField V)), S.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj t.G)) → ∃ P : PELUnif (maximalIdeal V) t, P.A = A ∧ HEq P.U.gen gen ∧ P.TorsionIso := by
  first | exact @GlobalTheory.UU.exists_pelUnif_of_cdvr | exact GlobalTheory.UU.exists_pelUnif_of_cdvr | (intros; apply GlobalTheory.UU.exists_pelUnif_of_cdvr <;> assumption)
