import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSquareZeroLiftLocal
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
theorem _root_.GlobalTheory.T.exists_square_zero_lift_local : ∀ {X : Scheme.{0}} {G : Over X} [GrpObj G] {S : Type} [Field S] (x0 : Sp S ⟶ X)
    {A B : Type} [CommRing A] [Algebra S A] [IsLocalRing A] [CommRing B] [Algebra S B] [IsLocalRing B]
    (q : A →ₐ[S] B), Function.Surjective q → ∀ [Module Sᵐᵒᵖ (RingHom.ker q)] [IsCentralScalar S (RingHom.ker q)]
    (hJ : RingHom.ker q ^ 2 = ⊥) (δ : overAt x0 A ⟶ G), Formalism.L2.Pj.homAt x0 q ≫ δ = 1 →
    ∃ ε : overAt x0 (TrivSqZeroExt S (RingHom.ker q)) ⟶ G,
      Formalism.L2.Pj.homAt x0 (TrivSqZeroExt.fstHom S S (RingHom.ker q)) ≫ ε = 1 ∧ Formalism.L2.Pj.homAt x0 (incl (RingHom.ker q) hJ) ≫ ε = δ := by
  first | exact @GlobalTheory.ExpUniqCh0.exists_factor_trivSqZeroExt | exact GlobalTheory.ExpUniqCh0.exists_factor_trivSqZeroExt | (intros; apply GlobalTheory.ExpUniqCh0.exists_factor_trivSqZeroExt <;> assumption)
