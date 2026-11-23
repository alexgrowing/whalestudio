import Mathlib
import Formalism.QuotientMetricDivisors.ProdFormula

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

namespace R0

variable {K : Type} [Field K] [StarRing K]

theorem map_inv_field {F : Type} [Field F] (f : K →+* F) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) : A⁻¹.map f = (A.map f)⁻¹ := by
  have hdet : (A.map f).det = f A.det := (RingHom.map_det f A).symm
  by_cases h : IsUnit A.det
  · symm
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ h, Matrix.map_one _ f.map_zero f.map_one]
  · have h' : ¬ IsUnit (A.map f).det := by
      rw [hdet, isUnit_iff_ne_zero, map_ne_zero f]
      rw [isUnit_iff_ne_zero] at h
      exact h
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h',
      Matrix.map_zero _ f.map_zero]

theorem conjTranspose_map (σ : K →+* ℂ) (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a))
    {m n : Type} (A : Matrix m n K) : Aᴴ.map σ = (A.map σ)ᴴ := by
  ext i j
  rw [Matrix.map_apply, Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, Matrix.map_apply, hσ]
  rfl

theorem conjTranspose_eq_of_posDef [NumberField K] (v0 : InfinitePlace K) (hv0 : IsConjAt v0)
    {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : (H.map v0.embedding).PosDef) : Hᴴ = H := by
  have h1 := conjTranspose_map v0.embedding hv0 H
  have h2 : (H.map v0.embedding)ᴴ = H.map v0.embedding := hH.isHermitian
  ext i j
  have h3 := congrFun (congrFun (h1.trans h2) i) j
  simp only [Matrix.map_apply] at h3
  exact v0.embedding.injective h3

theorem gramMat_conjTranspose {D m : ℕ} (Γ : Matrix (Fin D) (Fin D) K) (hΓ : Γᴴ = Γ)
    (e : Fin m → Fin D → K) :
    (Matrix.of fun a b => star (e a) ⬝ᵥ Γ.mulVec (e b))ᴴ =
      Matrix.of fun a b => star (e a) ⬝ᵥ Γ.mulVec (e b) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
  have h1 : star (star (e j) ⬝ᵥ Γ.mulVec (e i)) = star (e i) ⬝ᵥ Γᴴ.mulVec (e j) := by
    simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Matrix.conjTranspose_apply,
      Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    ring
  rw [h1, hΓ]

end R0

open R0 in
theorem gram_determinant_quotient_metric : GramDeterminantQuotientMetric := by
  intro K _ _ _ _ K0 hCM v0 hv0 n D H hK0 hpos P hsurj XQ hQ e
  have hH : Hᴴ = H := conjTranspose_eq_of_posDef v0 hv0 H (hpos v0)
  have hΓ : (quotGram P H)ᴴ = quotGram P H := by
    unfold quotGram
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv, hH, Matrix.mul_assoc]
  have hΓmap : (quotGram P H).map v0.embedding = ((XQ v0)⁻¹)ᴴ * (XQ v0)⁻¹ := by
    rw [(hQ v0).2]
    unfold quotGram
    rw [map_inv_field, Matrix.map_mul, Matrix.map_mul, map_inv_field, conjTranspose_map v0.embedding hv0]
  refine ⟨?_, ?_⟩
  · unfold gramR
    rw [← Matrix.det_conjTranspose, gramMat_conjTranspose _ hΓ e]
  · unfold gramR gram Formalism.HN.gramPl
    rw [RingHom.map_det]
    congr 1
    ext a c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Formalism.HermitianLatticesTheory.majAt,
      Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Pi.basisFun_repr]
    have hY : ∀ (Y : Matrix (Fin D) (Fin D) ℂ) (x y : Fin D → ℂ),
        ∑ i, star ((Y *ᵥ x) i) * (Y *ᵥ y) i = ∑ i, star (x i) * ((Yᴴ * Y) *ᵥ y) i := by
      intro Y x y
      have e1 : ∑ i, star ((Y *ᵥ x) i) * (Y *ᵥ y) i = star (Y *ᵥ x) ⬝ᵥ (Y *ᵥ y) := rfl
      have e2 : ∑ i, star (x i) * ((Yᴴ * Y) *ᵥ y) i = star x ⬝ᵥ ((Yᴴ * Y) *ᵥ y) := rfl
      rw [e1, e2, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
    rw [hY, ← hΓmap]
    have hv0' : ∀ a : K, v0.embedding (star a) = starRingEnd ℂ (v0.embedding a) := hv0
    simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Pi.star_apply, Matrix.map_apply, hv0']
    rfl

end Formalism.DivisionValues
