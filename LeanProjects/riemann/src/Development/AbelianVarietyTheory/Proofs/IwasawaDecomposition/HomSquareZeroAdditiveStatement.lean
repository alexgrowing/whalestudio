import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomSquareZeroAdditive
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulCoeEqZero
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory Formalism.L2.Pj GlobalTheory.Serre GlobalTheory.RayEv GlobalTheory.ExpUniqCh0

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_square_zero_additive : ∀ {X : Scheme.{0}} {G : Over X} [GrpObj G] {S : Type} [CommRing S] (x0 : Sp S ⟶ X)
    {V W : Type} [AddCommGroup V] [Module S V] [Module Sᵐᵒᵖ V] [IsCentralScalar S V]
    [AddCommGroup W] [Module S W] [Module Sᵐᵒᵖ W] [IsCentralScalar S W]
    (y : overAt x0 (TrivSqZeroExt S W) ⟶ G), Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.fstHom S S W) ≫ y = 1 →
    ∀ f g : W →ₗ[S] V, Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map (f + g)) ≫ y =
      (Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map f) ≫ y) * (Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.map g) ≫ y) := by
  first | exact @GlobalTheory.SqZeroAdd.map_add_comp | exact GlobalTheory.SqZeroAdd.map_add_comp | (intros; apply GlobalTheory.SqZeroAdd.map_add_comp <;> assumption)
