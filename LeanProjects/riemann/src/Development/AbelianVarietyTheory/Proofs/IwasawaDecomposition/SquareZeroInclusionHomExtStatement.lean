import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SquareZeroInclusionHomExt
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
theorem _root_.GlobalTheory.T.square_zero_inclusion_hom_ext : ∀ {X : Scheme.{0}} {G : Over X} {S : Type} [Field S] (x0 : Sp S ⟶ X)
    {A : Type} [CommRing A] [Algebra S A] [IsLocalRing A] (J : Ideal A) [Module Sᵐᵒᵖ J] [IsCentralScalar S J]
    (hJ : J ^ 2 = ⊥), Function.Injective (incl (S := S) J hJ) →
    ∀ u v : overAt x0 (TrivSqZeroExt S J) ⟶ G, Formalism.L2.Pj.homAt x0 (incl (S := S) J hJ) ≫ u = Formalism.L2.Pj.homAt x0 (incl (S := S) J hJ) ≫ v → u = v := by
  first | exact @GlobalTheory.ExpCancel.cancel_incl | exact GlobalTheory.ExpCancel.cancel_incl | (intros; apply GlobalTheory.ExpCancel.cancel_incl <;> assumption)
