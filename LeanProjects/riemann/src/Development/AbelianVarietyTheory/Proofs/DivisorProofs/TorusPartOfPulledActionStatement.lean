import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusPartOfPulledAction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_part_of_pulled_action : ∀ (O : Type) [CommRing O] (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (G : Over (Sp K)) [GrpObj G], IsSemiAbelian G → ∀ (i : OAct O G) (G' : Over (Sp Ω)) [GrpObj G'] (i' : OAct O G')
    (φ : G'.left ⟶ G.left), IsActPull i' i (spMap (algebraMap K Ω)) φ →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (u' : splitTorus (Sp Ω) X ⟶ G') (A : Over (Sp Ω)) [GrpObj A] (q' : G' ⟶ A) (j : OAct O A),
    IsAbelianScheme A → IsMonHom u' → IsKer u' q' → (∀ a, i'.act a ≫ q' = q' ≫ j.act a) →
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧
      ∃ (G₀ : Over (Sp F)) (_ : GrpObj G₀) (i₀ : OAct O G₀) (φ₀ : G₀.left ⟶ G.left)
        (Y : Type) (_ : AddCommGroup Y) (_ : Module.Free ℤ Y) (_ : Module.Finite ℤ Y) (u₀ : splitTorus (Sp F) Y ⟶ G₀)
        (B : Over (Sp F)) (_ : GrpObj B) (q₀ : G₀ ⟶ B) (j₀ : OAct O B) (ψ : A.left ⟶ B.left),
        IsActPull i₀ i (spMap (algebraMap K F)) φ₀ ∧ IsAbelianScheme B ∧ IsMonHom u₀ ∧ IsKer u₀ q₀ ∧
        (∀ a, i₀.act a ≫ q₀ = q₀ ≫ j₀.act a) ∧ IsActPull j j₀ (spMap (algebraMap F Ω)) ψ := by
  first | exact @GlobalTheory.TorusPart.exists_finite_torusExtension_act | exact GlobalTheory.TorusPart.exists_finite_torusExtension_act | (intros; apply GlobalTheory.TorusPart.exists_finite_torusExtension_act <;> assumption)
