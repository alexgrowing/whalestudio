import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.SymplSkew

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem herm_inv {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (a b : Fin n) :
    σ (J⁻¹ b a) = J⁻¹ a b := by
  have hmap : J.map σ = Jᵀ := by ext i j; simp [Matrix.transpose_apply, hJ.1 j i]
  have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have h1 : (J⁻¹).map σ * J.map σ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu]; simp
  have h2 : (J⁻¹).map σ = (J⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, ← hmap]; exact (Matrix.inv_eq_left_inv h1).symm
  have := congrFun (congrFun h2 b) a
  rw [Matrix.map_apply] at this
  rw [this, Matrix.transpose_apply]

noncomputable def cEquiv (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) : AEF F E ≃ₐ[AF F] AEF F E :=
  Algebra.TensorProduct.congr (AlgEquiv.refl) (AlgEquiv.ofAlgHom σ σ (AlgHom.ext fun e => hσ e) (AlgHom.ext fun e => hσ e))

theorem cEquiv_apply (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (z : AEF F E) : cEquiv σ hσ z = cAF σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cAF_cAF (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (z : AEF F E) : cAF σ (cAF σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    show (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) ((Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) (a ⊗ₜ e)) = a ⊗ₜ e
    simp [hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem cAF_incAF (σ : E →ₐ[F] E) (e : E) : cAF σ (incAF F E e) = incAF F E (σ e) := by
  show (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) ((1 : AF F) ⊗ₜ e) = (1 : AF F) ⊗ₜ σ e
  simp

theorem cAF_hOF (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) (x y : WOF F E nS nT) :
    cAF σ (hOF σ JS JT x y) = hOF σ JS JT y x := by
  unfold hOF
  simp only [map_sum, map_mul, cAF_incAF, cAF_cAF σ hσ, herm_inv hS, hT.1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem symplOF_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
    IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, σ ξ₀ = -ξ₀ → ∀ x y : WOF F E nS nT,
      symplOF σ JS JT ξ₀ y x = -symplOF σ JS JT ξ₀ x y := by
  intro F E _ _ _ _ _ σ hσ nS nT JS JT hS hT ξ₀ hξ x y
  unfold symplOF
  have hx : incAF F E ξ₀ = cAF σ (incAF F E (-ξ₀)) := by rw [cAF_incAF, ← hξ, hσ]
  rw [← cAF_hOF σ hσ hS hT x y]
  have key : incAF F E ξ₀ * cAF σ (hOF σ JS JT x y) = cEquiv σ hσ (incAF F E (-ξ₀) * hOF σ JS JT x y) := by
    rw [cEquiv_apply, map_mul, ← hx]
  rw [key, Algebra.trace_eq_of_algEquiv, map_neg, neg_mul, map_neg]

end GlobalTheory.SymplSkew
