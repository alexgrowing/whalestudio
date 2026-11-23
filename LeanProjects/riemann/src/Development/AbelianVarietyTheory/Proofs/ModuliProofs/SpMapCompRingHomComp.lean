import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

private theorem eval₂_monomial_X_mul_C_eq_C_mul_X_pow_degree {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R')
    (w : σ → R') (u : σ →₀ ℕ) (a : R) :
    MvPolynomial.eval₂ ((Polynomial.C : R' →+* Polynomial R').comp β) (fun i => Polynomial.X * Polynomial.C (w i))
        (MvPolynomial.monomial u a) =
      Polynomial.C (MvPolynomial.eval₂ β w (MvPolynomial.monomial u a)) * Polynomial.X ^ u.degree := by
  simp only [MvPolynomial.eval₂_monomial, RingHom.comp_apply, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← Polynomial.C_pow, ← map_prod, map_mul, Finsupp.degree_apply]
  ring

theorem coeff_eval₂_scale {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ) :
    (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F).coeff e =
      MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) := by
  refine MvPolynomial.induction_on' F (fun u a => ?_) (fun p q hp hq => ?_)
  · simp only [MvPolynomial.coe_eval₂Hom]
    rw [eval₂_monomial_X_mul_C_eq_C_mul_X_pow_degree, Polynomial.coeff_C_mul_X_pow,
      MvPolynomial.homogeneousComponent_of_mem ((MvPolynomial.mem_homogeneousSubmodule _ _).2
        (MvPolynomial.isHomogeneous_monomial a rfl))]
    split_ifs <;> simp
  · simp only [map_add, Polynomial.coeff_add, hp, hq]

theorem eval₂_homogeneousComponent_eq_zero {R R' σ : Type} [CommRing R] [CommRing R'] (β : R →+* R') (w : σ → R')
    (F : MvPolynomial σ R) (e : ℕ)
    (h : MvPolynomial.eval₂Hom ((LaurentPolynomial.C : R' →+* LaurentPolynomial R').comp β)
      (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (w i)) F = 0) :
    MvPolynomial.eval₂Hom β w (MvPolynomial.homogeneousComponent e F) = 0 := by
  rw [← coeff_eval₂_scale β w F e]
  have key : Polynomial.toLaurent (MvPolynomial.eval₂Hom ((Polynomial.C : R' →+* Polynomial R').comp β)
      (fun i => Polynomial.X * Polynomial.C (w i)) F) =
      MvPolynomial.eval₂Hom ((LaurentPolynomial.C : R' →+* LaurentPolynomial R').comp β)
        (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (w i)) F := by
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left]
    congr 1
    · ext r
      simp
    · funext i
      simp
  rw [h, ← map_zero Polynomial.toLaurent] at key
  rw [Polynomial.toLaurent_injective key, Polynomial.coeff_zero]

theorem spMap_comp_ringHom_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (β : A →+* B) (φ : B →+* C) :
    spMap φ ≫ spMap β = spMap (φ.comp β) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

private theorem secCoord_laurent_T_mul_C_of_secCoord {X Y : Scheme.{0}} {M : LB X} {σ : Type} {th : σ → M.Sec} {R' : Type}
    [CommRing R'] (y : Sp R' ⟶ Y) (a : Y ⟶ X) (v : σ → R') (h : SecCoord M th (y ≫ a) v) :
    SecCoord M th ((spMap (LaurentPolynomial.C : R' →+* LaurentPolynomial R') ≫ y) ≫ a)
      (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v i)) := by
  let u : (LaurentPolynomial R')ˣ := ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1),
    by rw [← LaurentPolynomial.T_add]; simp, by rw [← LaurentPolynomial.T_add]; simp⟩
  rw [Category.assoc]
  exact Coord.scale (Coord.baseChange h LaurentPolynomial.C) u

theorem ideals_homogeneous : (∀ (R σ : Type) [CommRing R] (Y X : Scheme.{0}) (s : Y ⟶ Sp R) (M : LB X) (th : σ → M.Sec) (a : Y ⟶ X), M.IsLB → (∀ F ∈ idealOf s M th a, ∀ e, MvPolynomial.homogeneousComponent e F ∈ idealOf s M th a)) ∧ (∀ (R σ₁ σ₂ : Type) [CommRing R] (Y X₁ X₂ : Scheme.{0}) (s : Y ⟶ Sp R) (M₁ : LB X₁) (th₁ : σ₁ → M₁.Sec) (a₁ : Y ⟶ X₁) (M₂ : LB X₂) (th₂ : σ₂ → M₂.Sec) (a₂ : Y ⟶ X₂), M₁.IsLB → M₂.IsLB → (∀ F ∈ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂, ∀ e, MvPolynomial.homogeneousComponent e F ∈ graphIdeal s M₁ th₁ a₁ M₂ th₂ a₂)) ∧ ∀ (R σ : Type) [CommRing R] (I : Ideal (MvPolynomial σ R)) (Z : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec), ProjRep I s M th → ProjRep (idealOf s M th (𝟙 Z)) s M th := by
  refine ⟨?_, ?_, ?_⟩
  · intro R σ _ Y X s M th a _ F hF e
    simp only [idealOf, Submodule.mem_iInf, RingHom.mem_ker] at hF ⊢
    intro R' _ β y v hyv
    have h0 := hF (LaurentPolynomial R') inferInstance (LaurentPolynomial.C.comp β)
      (spMap LaurentPolynomial.C ≫ y) (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v i))
      ⟨by rw [Category.assoc, hyv.1, spMap_comp_ringHom_comp], secCoord_laurent_T_mul_C_of_secCoord y a v hyv.2⟩
    exact eval₂_homogeneousComponent_eq_zero β v F e h0
  · intro R σ₁ σ₂ _ Y X₁ X₂ s M₁ th₁ a₁ M₂ th₂ a₂ _ _ F hF e
    simp only [graphIdeal, Submodule.mem_iInf, RingHom.mem_ker] at hF ⊢
    intro R' _ β y v₁ v₂ hyv
    have h0 := hF (LaurentPolynomial R') inferInstance (LaurentPolynomial.C.comp β)
      (spMap LaurentPolynomial.C ≫ y) (fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v₁ i))
      (fun i => LaurentPolynomial.C (v₂ i))
      ⟨by rw [Category.assoc, hyv.1, spMap_comp_ringHom_comp], secCoord_laurent_T_mul_C_of_secCoord y a₁ v₁ hyv.2.1,
        by rw [Category.assoc]; exact Coord.baseChange hyv.2.2 LaurentPolynomial.C⟩
    have hfun : (fun i : σ₁ × σ₂ => LaurentPolynomial.T 1 * LaurentPolynomial.C (v₁ i.1 * v₂ i.2)) =
        fun i => LaurentPolynomial.T 1 * LaurentPolynomial.C (v₁ i.1) * LaurentPolynomial.C (v₂ i.2) := by
      funext i
      rw [map_mul, ← _root_.mul_assoc]
    exact eval₂_homogeneousComponent_eq_zero β (fun i : σ₁ × σ₂ => v₁ i.1 * v₂ i.2) F e
      ((congrArg (fun g => MvPolynomial.eval₂Hom (LaurentPolynomial.C.comp β) g F) hfun).trans h0)
  · intro R σ _ I Z s M th hI
    have hle : ∀ F ∈ I, F ∈ idealOf s M th (𝟙 Z) := by
      intro F hF
      simp only [idealOf, Submodule.mem_iInf, RingHom.mem_ker]
      intro R' _ β y v hyv
      rw [Category.comp_id] at hyv
      exact (hI.2.1 R' β y v hyv.1 hyv.2).2 F hF
    refine ⟨hI.1, ?_, ?_⟩
    · intro R' _ β x v hx hc
      refine ⟨(hI.2.1 R' β x v hx hc).1, fun F hF => ?_⟩
      simp only [idealOf, Submodule.mem_iInf, RingHom.mem_ker] at hF
      exact hF R' inferInstance β x v ⟨hx, by rwa [Category.comp_id]⟩
    · intro R' _ β v hv hz
      exact hI.2.2 R' β v hv fun F hF => hz F (hle F hF)

end GlobalTheory.ZM
