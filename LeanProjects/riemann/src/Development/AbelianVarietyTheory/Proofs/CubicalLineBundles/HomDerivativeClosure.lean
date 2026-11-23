import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.HomDerivative

theorem isLieComb_inv {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {v x : epsR R ⟶ G} {a : R}
    (hv : IsTangent v) (hx : IsLieComb ![a] ![v] x) : IsLieComb ![-a] ![v] x⁻¹ := by
  obtain ⟨y, hy⟩ : ∃ y, IsLieComb ![-a] ![v] y :=
    ⟨_, (GlobalTheory.LieMultiple.isLieComb_one_iff_comp (-a) v _).2 rfl⟩
  have hsum := (GlobalTheory.LieMultiple.lieMultiple_calculus R G G v x y a (-a)).2.1 hv hx hy
  have hone := (GlobalTheory.LieMultiple.lieMultiple_calculus R G G v x y a (-a)).2.2.2.2.2 hv
  rw [add_neg_cancel] at hsum
  have hxy : x * y = 1 :=
    ((GlobalTheory.LieMultiple.isLieComb_one_iff_comp 0 v _).1 hsum).trans
      ((GlobalTheory.LieMultiple.isLieComb_one_iff_comp 0 v _).1 hone).symm
  rw [← eq_inv_of_mul_eq_one_right hxy]
  exact hy

theorem hom_derivative_closure : Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (R₁ : Type) [CommRing R₁] (ρ : R →+* R₁) (S : Set R₁), IsTangent t → (∀ a ∈ S, (∀ (P₁ Q₁ : Out.PolAV (Sp R₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR R₁ ⟶ P₁.A) (t₁ : epsR R₁ ⟶ Q₁.A), IsPolFibre ρ P P₁ φ₁ → IsPolFibre ρ Q Q₁ ψ₁ → IsVecOver ρ φ₁ v v₁ → IsVecOver ρ ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁))) → ∀ a ∈ AddSubgroup.closure S, (∀ (P₁ Q₁ : Out.PolAV (Sp R₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR R₁ ⟶ P₁.A) (t₁ : epsR R₁ ⟶ Q₁.A), IsPolFibre ρ P P₁ φ₁ → IsPolFibre ρ Q Q₁ ψ₁ → IsVecOver ρ φ₁ v v₁ → IsVecOver ρ ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) := by
  intro _ R _ P Q v t R₁ _ ρ S ht hS a ha
  induction ha using AddSubgroup.closure_induction with
  | mem a h => exact hS a h
  | zero =>
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    have hT : IsTangent t₁ := IsVecOver.isTangent hQ.2.1 ht₁ ht
    refine ⟨toUnit _ ≫ η, inferInstance, ?_⟩
    have h1 : v₁ ≫ toUnit P₁.A ≫ η[Q₁.A] = 1 := by
      rw [← Category.assoc, CartesianMonoidalCategory.toUnit_unique (v₁ ≫ toUnit _) (toUnit _)]
      rfl
    rw [h1]
    exact (GlobalTheory.LieMultiple.lieMultiple_calculus R₁ Q₁.A Q₁.A t₁ t₁ t₁ 0 0).2.2.2.2.2 hT
  | add a b _ _ iha ihb =>
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    have hT : IsTangent t₁ := IsVecOver.isTangent hQ.2.1 ht₁ ht
    obtain ⟨f, hf, hfa⟩ := iha P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    obtain ⟨g, hg, hgb⟩ := ihb P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    refine ⟨lift f g ≫ μ, inferInstance, ?_⟩
    change IsLieComb _ _ (v₁ ≫ (f * g))
    rw [MonObj.comp_mul]
    exact (GlobalTheory.LieMultiple.lieMultiple_calculus R₁ Q₁.A Q₁.A t₁ (v₁ ≫ f) (v₁ ≫ g) a b).2.1 hT hfa hgb
  | neg a _ iha =>
    intro P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    have hT : IsTangent t₁ := IsVecOver.isTangent hQ.2.1 ht₁ ht
    obtain ⟨f, hf, hfa⟩ := iha P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP hQ hv ht₁
    refine ⟨f⁻¹, inferInstance, ?_⟩
    rw [GrpObj.comp_inv]
    exact isLieComb_inv hT hfa

end GlobalTheory.HomDerivative
