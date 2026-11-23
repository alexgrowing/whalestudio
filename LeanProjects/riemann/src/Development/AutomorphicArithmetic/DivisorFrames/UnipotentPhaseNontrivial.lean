import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AutomorphicArithmetic.DivisorFrames.ExistsUnipotentHeisenberg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharExistsNeOneStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace UpperTheory.HermPhaseNe
open GlobalTheory.UnipMass

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem hA_herm {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (v w : Fin n → AE F E) : cA σ (hA σ J v w) = hA σ J w v := by
  simp only [hA, dotProduct, Matrix.mulVec, map_sum, map_mul, cA_cA hσ, incM, Matrix.map_apply, cA_inclR]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hJ y x]
  ring

private theorem hA_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : AE F E)
    (v w : Fin n → AE F E) : hA σ J v (a • w) = cA σ a * hA σ J v w := by
  simp only [hA, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => cA σ a * cA σ (w i)) = cA σ a • fun i => cA σ (w i) from rfl, Matrix.mulVec_smul,
    dotProduct_smul, smul_eq_mul]

private theorem hA_gram (σ : E →ₐ[F] E) {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin m) E)
    (z z' : Fin m → AE F E) :
    hA σ J (incM F A *ᵥ z) (incM F A *ᵥ z') = hA σ (Aᵀ * J * A.map σ) z z' := by
  have hc : (fun i => cA σ ((incM F A *ᵥ z') i)) = (incM F A).map (cA σ) *ᵥ fun i => cA σ (z' i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (incM F A) z' i
  have e : (incM F A)ᵀ * incM F J * (incM F A).map (cA σ) = incM F (Aᵀ * J * A.map σ) := by
    ext i j
    simp only [incM, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul, cA_inclR]
  rw [hA, hA, hc, ← Matrix.vecMul_transpose (incM F A) z, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, e]

private theorem vecMul_ne_zero {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (τ : E →+* ℂ) (θ : Matrix (Fin n) (Fin n) ℂ)
    (h : IsCartan (J.map τ) θ) (ξ : Fin n → E) (hξ : ξ ≠ 0) : ξ ᵥ* J ≠ 0 := by
  intro h0
  have e1 : θ *ᵥ (θ *ᵥ (τ ∘ ξ)) = τ ∘ ξ := by rw [Matrix.mulVec_mulVec, h.1, Matrix.one_mulVec]
  have hne : θ *ᵥ (τ ∘ ξ) ≠ 0 := by
    intro h1
    rw [h1, Matrix.mulVec_zero] at e1
    apply hξ
    funext i
    exact τ.injective (by simpa using (congrFun e1 i).symm)
  have h2 := h.2.2 _ hne
  have e2 : (τ ∘ ξ) ᵥ* J.map τ = 0 := by
    funext i
    rw [← RingHom.map_vecMul, h0]; simp
  rw [e1, Matrix.dotProduct_mulVec, e2] at h2
  simp at h2

private theorem exists_form_one {σ : E →ₐ[F] E} (hσ : ∀ a, σ (σ a) = a) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ξ : Fin n → E) (h : ξ ᵥ* J ≠ 0) : ∃ z₀, form σ J ξ z₀ = 1 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 h
  have hi' : (ξ ᵥ* J) i ≠ 0 := hi
  refine ⟨Pi.single i (σ ((ξ ᵥ* J) i)⁻¹), ?_⟩
  have e : (fun k => σ ((Pi.single i (σ ((ξ ᵥ* J) i)⁻¹) : Fin n → E) k)) = Pi.single i ((ξ ᵥ* J) i)⁻¹ := by
    funext k
    by_cases hk : k = i
    · subst hk; rw [Pi.single_eq_same, Pi.single_eq_same, hσ]
    · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk, map_zero]
  rw [form, e, Matrix.dotProduct_mulVec, dotProduct_single, mul_inv_cancel₀ hi']

end UpperTheory.HermPhaseNe

open UpperTheory.HermPhaseNe GlobalTheory.UnipMass in
theorem UpperTheory.unipotent_phase_nontrivial :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s r₁ s₁ : ℕ),
        B.IsGood σ → X.IsHerm σ B r s → X₁.IsHerm σ B r₁ s₁ → H.IsAdapted σ B X X₁ j₀ j₁ →
        ∀ ξ : Fin n₁ → E, ξ ≠ 0 → ∃ g ∈ unip σ X H, B.ψ (-GlobalTheory.IsoPhase.phase σ X H ξ g) ≠ 1 := by
  intro F E _ _ _ _ _ σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hB hX hX₁ hH ξ hξ
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hB.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨z₀, hz₀⟩ := exists_form_one hσ X₁.J ξ (vecMul_ne_zero X₁.J _ _ (hX₁.cartan w) ξ hξ)
  obtain ⟨s₀, hs₀⟩ := GlobalTheory.T.standard_adelic_char_exists_ne_one F B.ψ hB.std
  set z : Fin n₁ → AE F E := algebraMap (AF F) (AE F E) (⅟2 * s₀) • incV F z₀ with hz
  have h2 : algebraMap (AF F) (AE F E) (⅟2) + algebraMap (AF F) (AE F E) (⅟2) = 1 := by
    rw [← map_add, invOf_two_add_invOf_two, map_one]
  obtain ⟨g, hg, hgy, -⟩ := UpperTheory.exists_unipotent_heisenberg F E σ B n n₁ X X₁ H j₀ j₁ r s r₁ s₁ hB hX hX₁ hH z
    (-(algebraMap (AF F) (AE F E) (⅟2) * hA σ X₁.J z z)) (by
      rw [map_neg, map_mul, AlgHom.commutes, hA_herm hσ hX₁.herm]
      linear_combination (-hA σ X₁.J z z) * h2)
  refine ⟨g, hg, ?_⟩
  haveI : Nontrivial (AF F) := ⟨s₀, 0, fun h => hs₀ (by rw [h, AddChar.map_zero_eq_one])⟩
  have hr : Module.finrank (AF F) (AE F E) = 2 := by
    rw [Module.finrank_baseChange, hB.cm.2.2.1]
  have e : hA σ X.J (incV F (H.ι *ᵥ ξ)) (mat g⁻¹ *ᵥ incV F H.y) = algebraMap (AF F) (AE F E) (⅟2 * s₀) := by
    rw [hgy, hA_add_right, hA_add_right, hA_smul_right, hA_incV, hA_incV, (hH.orth ξ).1, (hH.orth ξ).2, map_zero,
      mul_zero, zero_add, add_zero, ← incM_mulVec_incV, hA_gram, hH.gram, hz, hA_smul_right, hA_incV, hz₀, map_one,
      mul_one, AlgHom.commutes]
  rw [GlobalTheory.IsoPhase.phase, neg_neg, e, Algebra.trace_algebraMap, hr, nsmul_eq_mul, ← mul_assoc, Nat.cast_ofNat,
    mul_invOf_self, one_mul]
  exact hs₀

end
