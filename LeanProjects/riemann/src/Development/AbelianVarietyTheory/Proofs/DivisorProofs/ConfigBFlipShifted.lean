import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairLoc
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

noncomputable section

namespace GlobalTheory.ShiftCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_smul' {v : Pl F} (τ : E →ₐ[F] Fv F v) (a : AF F) (z : AE F E) :
    piW τ (a • z) = evFin F v a * piW τ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, mul_add]
  | tmul b x =>
    rw [TensorProduct.smul_tmul']
    change splitProj τ (compFin F E v ((a • b) ⊗ₜ[F] x)) = evFin F v a * splitProj τ (compFin F E v (b ⊗ₜ[F] x))
    simp [compFin, mul_assoc]

theorem piW_inclR' {v : Pl F} (τ : E →ₐ[F] Fv F v) (x : E) : piW τ (inclR (F := F) (AF F) x) = τ x := by
  change splitProj τ (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = τ x
  simp [compFin]

theorem piW_cA'' {σ : E →ₐ[F] E} {v : Pl F} (τ : E →ₐ[F] Fv F v) (w : AE F E) :
    piW τ (cA σ w) = piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.ShiftCoords

namespace GlobalTheory.ShiftCoords

theorem mul_vecMulVec_mul' {R : Type} [CommRing R] {m n p q : Type} [Fintype n] [Fintype p]
    (A : Matrix m n R) (x : n → R) (y : p → R) (B : Matrix p q R) :
    A * Matrix.vecMulVec x y * B = Matrix.vecMulVec (A *ᵥ x) (y ᵥ* B) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, Matrix.vecMul, dotProduct]
  rw [Finset.sum_mul_sum, Finset.sum_comm]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.ShiftCoords

namespace GlobalTheory.ShiftCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sum_form {K : Type} [Field K] [Algebra F K] (σ : E →ₐ[F] E) (t : E →ₐ[F] K) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (z w : Fin n → E) :
    ∑ r, t (z r) * (J.map t *ᵥ fun s => t (σ (w s))) r = t (form σ J z w) := by
  simp only [form, dotProduct, Matrix.mulVec, Matrix.map_apply, map_sum, map_mul]

theorem form_swap_skew {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin n → E) : form σ J y x = -σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, cm_conj_conj hcm, hJ, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.ShiftCoords

namespace GlobalTheory.ShiftCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end GlobalTheory.ShiftCoords

namespace GlobalTheory.ShiftCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end GlobalTheory.ShiftCoords

namespace GlobalTheory.ShiftCoords

end GlobalTheory.ShiftCoords
