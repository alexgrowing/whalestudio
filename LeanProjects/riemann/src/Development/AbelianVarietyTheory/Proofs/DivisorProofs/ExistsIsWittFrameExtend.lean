import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameGLTwoDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCentreLawZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwoPlaneFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerRestrictsToOrthocomp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.DescB.PlaneTwo GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.TwoPlaneWitt

open Matrix
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField F] [NumberField E] in

theorem hE_smul_map {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c s t : E)
    (x y : Fin n → E) : hE σ (c • J.map σ) (s • x) (t • y) = σ s * t * c * σ (form σ J x y) := by
  simp only [hE, form, dotProduct, mulVec, Finset.mul_sum, map_sum, map_mul, Function.comp_apply, hσ, Pi.smul_apply,
    smul_eq_mul, Matrix.smul_apply, Matrix.map_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    show σ (s * x i) * (c * σ (J i j)) * (t * y j) = _
    rw [map_mul]; ring

omit [NumberField F] [NumberField E] in

theorem form_mulVec {σ : E →ₐ[F] E} {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin m) E)
    (u v : Fin m → E) : form σ J (ι *ᵥ u) (ι *ᵥ v) = form σ (ιᵀ * J * ι.map σ) u v := by
  have e : (⇑σ ∘ (ι *ᵥ v)) = ι.map σ *ᵥ (⇑σ ∘ v) := funext fun i => by simp [mulVec, dotProduct, map_sum]
  show (ι *ᵥ u) ⬝ᵥ J *ᵥ (⇑σ ∘ (ι *ᵥ v)) = u ⬝ᵥ (ιᵀ * J * ι.map σ) *ᵥ (⇑σ ∘ v)
  rw [e, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u, vecMul_transpose]

omit [NumberField F] [NumberField E] in

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (x y : Fin n → E) : form σ J x y = -σ (form σ J y x) := by
  simp only [form, dotProduct, mulVec, Finset.mul_sum, map_sum, map_mul, Function.comp_apply, hσ, hJ,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.TwoPlaneWitt

end
