import Mathlib
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem hom_deriv_baseChange : ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (R₀ : Type) [CommRing R₀] (ρ : R →+* R₀) (P₀ Q₀ : Out.PolAV (Sp R₀)) (φ : P₀.A.left ⟶ P.A.left) (ψ : Q₀.A.left ⟶ Q.A.left) (v₀ : epsR R₀ ⟶ P₀.A) (t₀ : epsR R₀ ⟶ Q₀.A) (f : P₀.A ⟶ Q₀.A) (a : R₀), IsPolFibre ρ P P₀ φ → IsPolFibre ρ Q Q₀ ψ → IsVecOver ρ φ v v₀ → IsVecOver ρ ψ t t₀ → IsMonHom f → IsLieComb ![a] ![t₀] (v₀ ≫ f) → ∀ (R₁ : Type) [CommRing R₁] (g : R₀ →+* R₁), (∀ (P₁ Q₁ : Out.PolAV (Sp R₁)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR R₁ ⟶ P₁.A) (t₁ : epsR R₁ ⟶ Q₁.A), IsPolFibre (g.comp ρ) P P₁ φ₁ → IsPolFibre (g.comp ρ) Q Q₁ ψ₁ → IsVecOver (g.comp ρ) φ₁ v v₁ → IsVecOver (g.comp ρ) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![g a] ![t₁] (v₁ ≫ f₁)) := by
  intro R _ P Q v t R₀ _ ρ P₀ Q₀ φ ψ v₀ t₀ f a hP hQ hv ht hf hlie R₁ _ g P₁ Q₁ φ₁ ψ₁ v₁ t₁ hP₁ hQ₁ hv₁ ht₁

  obtain ⟨φ', hφ', hφφ⟩ := PolFibre.cancel hP hP₁
  obtain ⟨ψ', hψ', hψψ⟩ := PolFibre.cancel hQ hQ₁
  have hv' : IsVecOver g φ' v₀ v₁ :=
    (PolFibre.vec_iff hP.2.1.1 hφ'.2.1.1.w hv).mpr (by rw [hφφ]; exact hv₁)
  have ht' : IsVecOver g ψ' t₀ t₁ :=
    (PolFibre.vec_iff hQ.2.1.1 hψ'.2.1.1.w ht).mpr (by rw [hψψ]; exact ht₁)

  have hsq : (φ' ≫ f.left) ≫ Q₀.A.hom = P₁.A.hom ≫ spMap g := by
    rw [Category.assoc, Over.w f]
    exact hφ'.2.1.1.w
  let f₁ : P₁.A ⟶ Q₁.A :=
    Over.homMk (hψ'.2.1.1.lift (φ' ≫ f.left) P₁.A.hom hsq) (hψ'.2.1.1.lift_snd _ _ _)
  have hf₁ : f₁.left ≫ ψ' = φ' ≫ f.left := hψ'.2.1.1.lift_fst _ _ _
  have : IsMonHom f := hf
  refine ⟨f₁, GlobalTheory.UU.isMonHom_of_over_isMonHom hφ'.2.1 hψ'.2.1 f f₁ hf₁, ?_⟩

  have hw : (v₁ ≫ f₁).left ≫ ψ' = spMap (Chart.dualMapR g) ≫ (v₀ ≫ f).left := by
    have e : v₁.left ≫ φ' = spMap (Chart.dualMapR g) ≫ v₀.left := hv'
    simp only [Over.comp_left, Category.assoc, hf₁]
    rw [← Category.assoc, e, Category.assoc]
  have key := (lieComb_baseChange R₀ R₁ g Q₀.A Q₁.A ψ' hψ'.2.1 1 ![t₀] (v₀ ≫ f) ![a] ![t₁] (v₁ ≫ f₁)
    (by intro j; fin_cases j; exact ht') hlie).mp hw
  convert key using 1
  funext i
  fin_cases i
  rfl

end GlobalTheory
