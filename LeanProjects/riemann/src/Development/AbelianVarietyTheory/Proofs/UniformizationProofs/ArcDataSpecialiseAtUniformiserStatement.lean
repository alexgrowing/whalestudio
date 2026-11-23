import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiser
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arcData_specialise_at_uniformiser : Laws → Laws2 → DVR.TwistBaseChangeStatement → UnifBaseChangeSt → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (Dm : Geo.Tor.Datum H) (l : Geo.Tor.Level H) (Xo : Geo.Tor.Moduli Dm l) (c : Geo.Tor.Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Geo.Tor.Model Xo c β) (V : Type) [CommRing V] [IsDomain V] [CharZero V] [IsDiscreteValuationRing V] (b : O →+* V) (ϖ : V) (a : Geo.Tor.ArcIn Dm l β V b), Irreducible ϖ → IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (ev : PowerSeries V →+* V), (∀ x, ev (PowerSeries.C x) = x) → ev PowerSeries.X = ϖ → ∀ χ : Geo.Tor.Sp (PowerSeries V) ⟶ Y.X, χ ≫ Y.s = Geo.Tor.spMap (PowerSeries.C (R := V)) ≫ Geo.Tor.spMap b → Set.range (jK V ≫ Geo.Tor.spMap ev ≫ χ) ⊆ Set.range Y.j → Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := V)) PowerSeries.X χ → Y.HasArcData a (Ideal.span {ϖ}) (RingHom.id V) ϖ (Geo.Tor.spMap ev ≫ χ) := by
  first | exact @GlobalTheory.hasArcData_specialise | exact GlobalTheory.hasArcData_specialise | (intros; apply GlobalTheory.hasArcData_specialise <;> assumption)
