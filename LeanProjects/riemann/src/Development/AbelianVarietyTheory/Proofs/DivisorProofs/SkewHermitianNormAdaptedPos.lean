import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdelesInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

noncomputable section
namespace GlobalTheory.TorFinArch

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem herm_map_eq (σ : E →ₐ[F] E) (hτσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) (hσ : ∀ x, σ (σ x) = x)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (p q : Fin n → E) (τ : E →+* ℂ) :
    (star (fun i => τ (p i)) ᵥ* (c • J.map σ).map τ) ⬝ᵥ (fun i => τ (q i)) = τ (c * σ (form σ J p q)) := by
  simp only [form, dotProduct, Matrix.vecMul, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul, Pi.star_apply, hσ, hτσ, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : E) (p q : Fin n → E) :
    form σ J p (fun i => a * q i) = σ a * form σ J p q := by
  simp only [form, dotProduct, Matrix.mulVec, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : E) (p q : Fin n → E) :
    form σ J (fun i => a * p i) q = a * form σ J p q := by
  simp only [form, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem isotropic_dual_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ τ : E →+* ℂ, (star (fun i => τ (H'.x i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (H'.x i)) = 0 ∧ (star (fun i => τ (c⁻¹ * H'.y i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (c⁻¹ * H'.y i)) = 0 ∧ (star (fun i => τ (H'.x i)) ᵥ* (c • W.J.map σ).map τ) ⬝ᵥ (fun i => τ (c⁻¹ * H'.y i)) = 1 := by
  intro F E _ _ _ _ _ σ B hcm d r s W _ hσ c hc _ d₁ W₁ H' i₀ i₁ hH τ
  have hτσ := hcm.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [herm_map_eq σ hτσ hσ, hH.xx, map_zero, mul_zero, map_zero]
  · rw [herm_map_eq σ hτσ hσ, form_smul_right, form_smul_left, hH.yy, mul_zero, mul_zero, map_zero, mul_zero, map_zero]
  · rw [herm_map_eq σ hτσ hσ, form_smul_right, hH.xy, mul_one, hσ, mul_inv_cancel₀ hc, map_one]

end GlobalTheory.TorFinArch
