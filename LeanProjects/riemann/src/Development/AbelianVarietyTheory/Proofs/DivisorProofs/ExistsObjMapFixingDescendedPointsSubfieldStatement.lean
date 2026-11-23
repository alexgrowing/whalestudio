import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapFixingDescendedPointsSubfield
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtalePointOfExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomDescendsAlgClosedCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSabMapOfGrpPullbackRespectingActionBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_objMap_fixing_descended_points_subfield : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} {Bb : Type} [CommRing Bb] {b : Base l Bb} (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (k₀ : Subfield K), IsAlgClosed k₀ → ∀ {s : Sp K ⟶ Sp Bb} (o : Obj D l b s) (B₀ : Over (Sp k₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (π : o.t.G.left ⟶ B₀.left), IsAbelianScheme B₀ → M₀.IsLB → IsGrpPullback o.t.G B₀ (spMap k₀.subtype) π → LBIso o.t.PP.L (M₀.pull π) → ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∃ n : ObjMap o o (spMap (σ : K →+* K)), ∀ x : Sp K ⟶ o.t.G.left, x ≫ o.t.G.hom = 𝟙 _ → (∃ x₀ : Sp k₀ ⟶ B₀.left, x ≫ π = spMap k₀.subtype ≫ x₀) → x ≫ n.toSABMap.φ = spMap (σ : K →+* K) ≫ x := by
  first | exact @GlobalTheory.AutLift.exists_objMap_fixing_descended_points | exact GlobalTheory.AutLift.exists_objMap_fixing_descended_points | (intros; apply GlobalTheory.AutLift.exists_objMap_fixing_descended_points <;> assumption)
