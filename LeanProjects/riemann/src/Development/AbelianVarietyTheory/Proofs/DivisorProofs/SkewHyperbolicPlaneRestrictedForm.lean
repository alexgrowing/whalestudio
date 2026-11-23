import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCoordinateAdditive
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.UnipDom.MatEq

open GlobalTheory.ThK.UnipDom.Additive

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incV_add {n : ℕ} (v w : Fin n → E) : incV F (v + w) = incV F v + incV F w := by
  funext i; simp [incV]

theorem incV_smul {n : ℕ} (s : E) (v : Fin n → E) :
    incV F (s • v) = inclR (F := F) (AF F) s • incV F v := by
  funext i; simp [incV]

theorem fA_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w w' : Fin n → AE F E) :
    fA σ J v (w + w') = fA σ J v w + fA σ J v w' := by
  have : (fun i => cA σ ((w + w') i)) = (fun i => cA σ (w i)) + (fun i => cA σ (w' i)) := by
    funext i; simp
  simp only [fA, this, Matrix.mulVec_add, dotProduct_add]

theorem fA_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : AE F E)
    (v w : Fin n → AE F E) : fA σ J v (c • w) = cA σ c * fA σ J v w := by
  have : (fun i => cA σ ((c • w) i)) = cA σ c • (fun i => cA σ (w i)) := by
    funext i; simp
  simp only [fA, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem fA_unitary {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (u : UA σ J)
    (v w : Fin n → AE F E) : fA σ J (mat u *ᵥ v) (mat u *ᵥ w) = fA σ J v w := by
  have hu : (mat u)ᵀ * incM F J * (mat u).map (cA σ) = incM F J := u.2
  have hc : (fun i => cA σ ((mat u *ᵥ w) i)) = (mat u).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (mat u) w i
  simp only [fA, hc]
  rw [← Matrix.vecMul_transpose (mat u) v, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hu]

theorem fA_mulVec_left (σ : E →ₐ[F] E) {m n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (N : Matrix (Fin n) (Fin m) (AE F E)) (z : Fin m → AE F E) (w : Fin n → AE F E) :
    fA σ J (N *ᵥ z) w = z ⬝ᵥ fun j => fA σ J (N *ᵥ Pi.single j 1) w := by
  simp only [fA]
  rw [← Matrix.vecMul_transpose N z, ← Matrix.dotProduct_mulVec]
  congr 1
  funext j
  rw [Matrix.mulVec_single_one]
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

theorem form_swap {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hσ : ∀ e, σ (σ e) = e)
    (hsk : ∀ i j, σ (J j i) = -J i j) (v w : Fin n → E) : form σ J v w = -σ (form σ J w v) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hsk, Finset.mul_sum, mul_neg,
    Finset.sum_neg_distrib, neg_neg]
  simp only [neg_mul, mul_neg, Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

end GlobalTheory.ThK.UnipDom.MatEq
