import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBaseIdentityAlongMorphism
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fromBase_identity_along_morphism : ∀ {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* R), FromBase Q τ₀ ιb → ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp W₀ ⟶ B₀.left)) (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1])) (β : Q.P.A.left ⟶ B₀.left) (w : LB.Iso Q.P.L (M₀.pull β)), IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.P.A B₀ (spMap ιb) β ∧ w.IsGen ∧ (∀ a, cpt Q a ≫ β = spMap ιb ≫ c₀ a) ∧ (∀ a b, (τ₁ a b).IsGen) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp R) (a b : Q.X) (zz : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι) (J₀ : (Z ⟶ B₀.left) → M₀.ι), Good Q.P.L zz J → Good M₀ zz J₀ → val (τ₀ a b) r zz J = gm (r ≫ cpt Q (a + b)) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q (a + b) ≫ β), J (r ≫ cpt Q (a + b)))) * (gm (r ≫ cpt Q a) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q a ≫ β), J (r ≫ cpt Q a))))⁻¹ * (gm (r ≫ cpt Q b) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q b ≫ β), J (r ≫ cpt Q b))))⁻¹ * gm (r ≫ cpt Q 0) zz _ (w.s (fun _ => J₀ (r ≫ cpt Q 0 ≫ β), J (r ≫ cpt Q 0))) * val (τ₁ a b) (r ≫ spMap ιb) zz J₀ := by
  first | exact @GlobalTheory.UChart.FromBaseAlong.fromBase_along | exact GlobalTheory.UChart.FromBaseAlong.fromBase_along | (intros; apply GlobalTheory.UChart.FromBaseAlong.fromBase_along <;> assumption)
