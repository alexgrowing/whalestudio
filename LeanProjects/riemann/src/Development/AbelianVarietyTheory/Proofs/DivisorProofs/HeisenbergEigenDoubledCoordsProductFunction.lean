import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromColsMemLatDbl
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblBoxRho

section Alg

variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] in

theorem symp_dbl_toCols (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α (β ⊕ β) E) :
    symp (R := R) c ξ JA (dbl JB) x y =
      symp (R := R) c ξ JA JB x.toCols₁ y.toCols₁ - symp (R := R) c ξ JA JB x.toCols₂ y.toCols₂ := by
  unfold symp
  rw [← map_sub, ← mul_sub]
  congr 2
  simp only [hTens, dbl, Fintype.sum_sum_type, Matrix.toCols₁_apply, Matrix.toCols₂_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib, sub_eq_add_neg]

theorem star_apply_eq_neg (ψ : AddChar R ℂ) (hψ : ∀ t, ‖ψ t‖ = 1) (t : R) : star (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ]
  simp

variable [Invertible (2 : R)]

theorem schr_boxFun (ψ : AddChar R ℂ) (hψ : ∀ t, ‖ψ t‖ = 1) {κ : Type} [Fintype κ] (w₁ w₂ : (κ → R) × (κ → R))
    (φ₁ φ₂ : (κ → R) → ℂ) :
    schr ψ (Sum.elim w₁.1 w₂.1, Sum.elim w₁.2 (-w₂.2)) (boxFun φ₁ fun x => star (φ₂ x)) =
      boxFun (schr ψ w₁ φ₁) fun x => star (schr ψ w₂ φ₂ x) := by
  funext x
  have e : x = Sum.elim (x ∘ Sum.inl) (x ∘ Sum.inr) := (Sum.elim_comp_inl_inr x).symm
  have e1 : (x + Sum.elim w₁.1 w₂.1) ∘ Sum.inl = x ∘ Sum.inl + w₁.1 := rfl
  have e2 : (x + Sum.elim w₁.1 w₂.1) ∘ Sum.inr = x ∘ Sum.inr + w₂.1 := rfl
  have e3 : x ⬝ᵥ Sum.elim w₁.2 (-w₂.2) = (x ∘ Sum.inl) ⬝ᵥ w₁.2 - (x ∘ Sum.inr) ⬝ᵥ w₂.2 := by
    conv_lhs => rw [e]
    rw [sumElim_dotProduct_sumElim, dotProduct_neg, sub_eq_add_neg]
  simp only [schr, boxFun, e1, e2, e3, sumElim_dotProduct_sumElim, dotProduct_neg, star_mul', star_apply_eq_neg ψ hψ]
  rw [mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
  congr 2
  ring

end Alg

theorem boxrho : ∀ {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
    {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] (ξ ξ' : E) (JA : Matrix α α E) (JB : Matrix β β E)
    {κ : Type} [Fintype κ] (d : Darboux (symp c ξ JA JB) κ) (dd : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)),
    IsDblCoord c ξ JA JB d dd → ∀ ψ : AddChar R ℂ, (∀ t, ‖ψ t‖ = 1) → ∀ (Λ : Set (Matrix α β E)) (f : (κ → R) → ℂ),
    (∀ w ∈ Λ, d.rho ψ w f = ψ (⅟(2 : R) * symp c ξ' JA JB w w) • f) →
    ∀ z : Matrix α (β ⊕ β) E, z.toCols₁ ∈ Λ → z.toCols₂ ∈ Λ →
      dd.rho ψ z (boxFun f (fun x => star (f x))) = ψ (⅟(2 : R) * symp c ξ' JA (dbl JB) z z) • boxFun f (fun x => star (f x)) := by
  intro R _ _ E _ _ c α β _ _ _ _ ξ ξ' JA JB κ _ d dd hD ψ hψ Λ f hf z h₁ h₂
  have hz : Matrix.fromCols z.toCols₁ z.toCols₂ = z := Matrix.fromCols_toCols z
  have he := hD z.toCols₁ z.toCols₂
  rw [hz] at he
  have e₁ := hf _ h₁
  have e₂ := hf _ h₂
  simp only [Darboux.rho] at e₁ e₂
  rw [Darboux.rho, he, schr_boxFun ψ hψ, e₁, e₂, symp_dbl_toCols]
  funext x
  simp only [boxFun, Pi.smul_apply, smul_eq_mul, star_mul', star_apply_eq_neg ψ hψ, mul_sub]
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

end GlobalTheory.DblBoxRho
