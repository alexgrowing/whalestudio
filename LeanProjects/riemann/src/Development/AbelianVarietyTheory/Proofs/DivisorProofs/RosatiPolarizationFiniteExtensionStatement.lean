import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiPolarizationFiniteExtension
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TorusPart

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rosati_polarization_finite_extension : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (c : O →+* O) (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ (j₀ : OAct O B) (P : Out.PolAV (Sp Ω))
    (j : OAct O P.A) (ψ : P.A.left ⟶ B.left), IsActPull j j₀ (spMap (algebraMap K Ω)) ψ → IsRosati c P j →
    ∃ F : IntermediateField K Ω, FiniteDimensional K F ∧ ∃ (P₁ : Out.PolAV (Sp F)) (j₁ : OAct O P₁.A)
      (ψ₁ : P₁.A.left ⟶ B.left), IsActPull j₁ j₀ (spMap (algebraMap K F)) ψ₁ ∧ IsRosati c P₁ j₁ := by
  first | exact @GlobalTheory.TorusPart.exists_finite_polDescent | exact GlobalTheory.TorusPart.exists_finite_polDescent | (intros; apply GlobalTheory.TorusPart.exists_finite_polDescent <;> assumption)
