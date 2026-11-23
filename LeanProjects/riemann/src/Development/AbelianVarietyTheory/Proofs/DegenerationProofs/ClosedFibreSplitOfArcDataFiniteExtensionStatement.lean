import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedFibreSplitOfArcDataFiniteExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedFibre_split_of_arcData_finite_extension : Laws → Laws2 → Laws3 → Laws4 → Laws5 → Laws6 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype) (O' : Type) [CommRing O'] [IsDomain O'] [CharZero O'] (b : c.V W₀ →+* O') (a : ArcIn D l (c.V W₀).subtype O' b) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (f : O' →+* V) (u : V), (∀ x, x ≠ 0 → IsUnit (f x)) → ¬ IsUnit u → ∀ (χ : Sp V ⟶ Y.X) (y : Sp (FractionRing V) ⟶ Xo.XF c), y ≫ Y.j = jK V ≫ χ → ∀ (t : SAB H (Sp V)) (_ : SABMap t Y.t χ) (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V' → ∀ g : V →+* V', Function.Injective g → g.Finite → Y.HasArcData a (IsLocalRing.maximalIdeal V') (g.comp f) (g u) (spMap g ≫ χ) → SplitOver t.G (IsLocalRing.maximalIdeal V) := by
  first | exact @GlobalTheory.SplitAtTrait.splitOver_of_hasArcData | exact GlobalTheory.SplitAtTrait.splitOver_of_hasArcData | (intros; apply GlobalTheory.SplitAtTrait.splitOver_of_hasArcData <;> assumption)
