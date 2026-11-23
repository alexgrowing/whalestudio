import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisAutConjugateFieldPointsCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_aut_conjugate_field_points_cover : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] [IsGalois Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ (K : Type) [Field K] [CharZero K] (y y' : Sp K ⟶ M₂.Z), y ≫ q = y' ≫ q → ∃ (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) (s : M₂.Z ⟶ M₂.Z), M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ y ≫ s = y' ∧ ∀ b : Ω₂, M₂.val y' b = M₂.val y (σ b) := by
  first | exact @GlobalTheory.Poinc.FieldConj.exists_aut_eq_of_comp_eq | exact GlobalTheory.Poinc.FieldConj.exists_aut_eq_of_comp_eq | (intros; apply GlobalTheory.Poinc.FieldConj.exists_aut_eq_of_comp_eq <;> assumption)
