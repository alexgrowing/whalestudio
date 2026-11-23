import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

namespace GlobalTheory.ThK.FrameGram

theorem gram_apply {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (Q : Matrix (Fin n) (Fin m) E) (a b : Fin m) :
    (Qᵀ * J * Q.map σ) a b = form σ J (fun r => Q r a) (fun r => Q r b) := by
  simp only [form, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem form_swap {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = -J i j)
    (u v : Fin n → E) : form σ J v u = -σ (form σ J u v) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [hJ l k]; ring

theorem col_eq {E : Type} [Field E] {n m : ℕ} (ι : Matrix (Fin n) (Fin m) E) (a : Fin m) :
    (fun r => ι r a) = ι *ᵥ Pi.single a 1 := by
  funext r
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem frame_gram : ∀ {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (d₁ : ℕ)
    (J : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E) (J₁ : Matrix (Fin d₁) (Fin d₁) E) (x y : Fin (d₁ + 2) → E)
    (ι : Matrix (Fin (d₁ + 2)) (Fin d₁) E) (Q : Matrix (Fin (d₁ + 2)) (Fin (d₁ + 2)) E),
    (∀ a, σ (σ a) = a) → (∀ i j, σ (J j i) = -J i j) → form σ J x x = 0 → form σ J y y = 0 → form σ J x y = 1 →
    (∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) → ιᵀ * J * ι.map σ = J₁ →
    (∀ r a, Q r (Fin.castAdd 2 a) = ι r a) → (∀ r, Q r (Fin.natAdd d₁ 0) = x r) → (∀ r, Q r (Fin.natAdd d₁ 1) = y r) →
    (∀ a a', (Qᵀ * J * Q.map σ) (Fin.castAdd 2 a) (Fin.castAdd 2 a') = J₁ a a') ∧
      (∀ a t, (Qᵀ * J * Q.map σ) (Fin.castAdd 2 a) (Fin.natAdd d₁ t) = 0) ∧
      (∀ t a, (Qᵀ * J * Q.map σ) (Fin.natAdd d₁ t) (Fin.castAdd 2 a) = 0) ∧
      (Qᵀ * J * Q.map σ) (Fin.natAdd d₁ 0) (Fin.natAdd d₁ 0) = 0 ∧ (Qᵀ * J * Q.map σ) (Fin.natAdd d₁ 1) (Fin.natAdd d₁ 1) = 0 ∧
      (Qᵀ * J * Q.map σ) (Fin.natAdd d₁ 0) (Fin.natAdd d₁ 1) = 1 ∧ (Qᵀ * J * Q.map σ) (Fin.natAdd d₁ 1) (Fin.natAdd d₁ 0) = -1 := by
  intro F E _ _ _ σ d₁ J J₁ x y ι Q hσ hJ hxx hyy hxy hι hJ₁ hQι hQx hQy
  have cQ : ∀ a, (fun r => Q r (Fin.castAdd 2 a)) = ι *ᵥ Pi.single a 1 := by
    intro a; rw [← col_eq]; funext r; exact hQι r a
  have cx : (fun r => Q r (Fin.natAdd d₁ 0)) = x := funext hQx
  have cy : (fun r => Q r (Fin.natAdd d₁ 1)) = y := funext hQy
  have ht : ∀ t : Fin 2, (fun r => Q r (Fin.natAdd d₁ t)) = x ∨ (fun r => Q r (Fin.natAdd d₁ t)) = y := by
    intro t; fin_cases t
    · left; exact cx
    · right; exact cy
  have orth : ∀ a (t : Fin 2), form σ J (ι *ᵥ Pi.single a 1) (fun r => Q r (Fin.natAdd d₁ t)) = 0 := by
    intro a t
    rcases ht t with h | h <;> rw [h]
    · exact (hι _).1
    · exact (hι _).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a a'
    rw [gram_apply, cQ, cQ, ← col_eq, ← col_eq, ← hJ₁, gram_apply]
  · intro a t
    rw [gram_apply, cQ, orth]
  · intro t a
    rw [gram_apply, cQ, form_swap σ J hσ hJ, orth, map_zero, neg_zero]
  · rw [gram_apply, cx, hxx]
  · rw [gram_apply, cy, hyy]
  · rw [gram_apply, cx, cy, hxy]
  · rw [gram_apply, cx, cy, form_swap σ J hσ hJ, hxy, map_one]

end GlobalTheory.ThK.FrameGram
