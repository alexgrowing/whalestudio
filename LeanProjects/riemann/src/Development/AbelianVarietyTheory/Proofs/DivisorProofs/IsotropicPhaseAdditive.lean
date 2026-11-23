import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IsoPhaseAdd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hA_smul_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : AE F E) (v v' w : Fin n → AE F E) :
    GlobalTheory.UnipMass.hA σ J (c • v + v') w = c * GlobalTheory.UnipMass.hA σ J v w + GlobalTheory.UnipMass.hA σ J v' w := by
  unfold GlobalTheory.UnipMass.hA
  rw [add_dotProduct, smul_dotProduct, smul_eq_mul]

theorem cA_mulVec (σ : E →ₐ[F] E) {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE F E)) (w : Fin n → AE F E) :
    (fun i => cA σ ((M *ᵥ w) i)) = M.map (cA σ) *ᵥ fun i => cA σ (w i) := by
  ext i
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem hA_mat_mulVec (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (v w : Fin n → AE F E) :
    GlobalTheory.UnipMass.hA σ J (mat g *ᵥ v) (mat g *ᵥ w) = GlobalTheory.UnipMass.hA σ J v w := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  unfold GlobalTheory.UnipMass.hA
  rw [cA_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hg]

theorem phase_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' : ℕ), IsCMExt F E σ → W.IsSkew σ B r' s' →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ w : Fin d₁ → E, ∀ u ∈ unip σ W H', ∀ v ∈ unip σ W H',
      GlobalTheory.IsoPhase.phase σ W H' w (u * v) = GlobalTheory.IsoPhase.phase σ W H' w u + GlobalTheory.IsoPhase.phase σ W H' w v := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r' s' _ _ hH w u hu v hv
  rw [GlobalTheory.UnipCT.unip_eq] at hu hv
  have hui := (GlobalTheory.UnipCT.unipSet σ W H').inv_mem hu
  set a : Fin d → AE F E := incV F (H'.ι *ᵥ w) with ha
  set X : Fin d → AE F E := incV F H'.x
  set Y : Fin d → AE F E := incV F H'.y

  have haY : GlobalTheory.UnipMass.hA σ W.J a Y = 0 := by
    rw [ha, GlobalTheory.UnipMass.hA_incV, (hH.orth w).2, map_zero]

  set t : Fin d → AE F E := mat u⁻¹ *ᵥ Y - Y with ht
  have hXt : GlobalTheory.UnipMass.hA σ W.J X t = 0 := by
    have hx : mat u⁻¹ *ᵥ X = X := hui.1
    have h1 := hA_mat_mulVec σ u⁻¹ X Y
    rw [hx] at h1
    have h2 : mat u⁻¹ *ᵥ Y = t + Y := by rw [ht, sub_add_cancel]
    rw [h2, GlobalTheory.UnipMass.hA_add_right] at h1
    exact add_eq_right.1 h1

  obtain ⟨c, hc⟩ := hv.2 (incV F w)
  rw [GlobalTheory.UnipMass.incM_mulVec_incV] at hc
  have hc' : mat v *ᵥ a = a + c • X := hc
  have hvt : GlobalTheory.UnipMass.hA σ W.J a (mat v⁻¹ *ᵥ t) = GlobalTheory.UnipMass.hA σ W.J a t := by
    have h1 := hA_mat_mulVec σ v a (mat v⁻¹ *ᵥ t)
    rw [Matrix.mulVec_mulVec, ← GlobalTheory.UnipCT.mat_mul', mul_inv_cancel, hc'] at h1
    have h3 : mat (1 : UA σ W.J) = 1 := rfl
    rw [h3, Matrix.one_mulVec, add_comm, hA_smul_add_left, hXt, mul_zero, zero_add] at h1
    exact h1.symm
  have key : GlobalTheory.UnipMass.hA σ W.J a (mat (u * v)⁻¹ *ᵥ Y) =
      GlobalTheory.UnipMass.hA σ W.J a (mat u⁻¹ *ᵥ Y) + GlobalTheory.UnipMass.hA σ W.J a (mat v⁻¹ *ᵥ Y) := by
    have e1 : mat u⁻¹ *ᵥ Y = Y + t := by rw [ht, add_sub_cancel]
    rw [mul_inv_rev, GlobalTheory.UnipCT.mat_mul', ← Matrix.mulVec_mulVec, e1, Matrix.mulVec_add, GlobalTheory.UnipMass.hA_add_right,
      hvt, GlobalTheory.UnipMass.hA_add_right, haY, zero_add, add_comm]
  unfold GlobalTheory.IsoPhase.phase
  rw [← ha, key, map_add, neg_add]

end GlobalTheory.IsoPhaseAdd
