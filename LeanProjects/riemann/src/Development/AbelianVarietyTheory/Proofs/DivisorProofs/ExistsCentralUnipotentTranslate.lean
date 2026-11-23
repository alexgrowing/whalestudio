import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.UnipMass.CentralShift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mat_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g g' : UA σ J) :
    mat (g * g') = mat g * mat g' := rfl

theorem mat_one' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

theorem mat_inv_mul' {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) :
    mat g⁻¹ * mat g = 1 := by
  rw [← mat_mul', inv_mul_cancel, mat_one']

theorem hA_mat (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) (v w : Fin n → AE F E) :
    hA σ J (mat g *ᵥ v) (mat g *ᵥ w) = hA σ J v w := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have hc : (fun i => cA σ ((mat g *ᵥ w) i)) = (mat g).map (cA σ) *ᵥ fun i => cA σ (w i) := by
    funext i; exact RingHom.map_mulVec (cA σ).toRingHom (mat g) w i
  rw [hA, hA, hc, ← Matrix.vecMul_transpose (mat g) v, ← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec]
  rw [← Matrix.mul_assoc, hg]

variable {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {H' : Plane E d d₁}

theorem unip_fix (u : UA σ W.J) (hu : u ∈ unip σ W H') : mat u *ᵥ incV F H'.x = incV F H'.x := by
  induction hu using Subgroup.closure_induction with
  | mem g hg => exact hg.1
  | one => rw [mat_one', Matrix.one_mulVec]
  | mul g g' _ _ hg hg' => rw [mat_mul', ← Matrix.mulVec_mulVec, hg', hg]
  | inv g _ hg =>
    conv_lhs => rw [← hg]
    rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]

end GlobalTheory.UnipMass.CentralShift

namespace GlobalTheory.UnipMass.CentralShift

open GlobalTheory.UnipMass

theorem exists_central_shift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r' s' : ℕ), IsCMExt F E σ → W.IsSkew σ B r' s' →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ t : AF F, ∃ z : UA σ W.J, z ∈ unip σ W H' ∧ (∀ u ∈ unip σ W H', z * u = u * z) ∧
      mat z⁻¹ *ᵥ incV F H'.y = incV F H'.y - algebraMap (AF F) (AE F E) t • incV F H'.x := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r' s' hcm hW hH t
  have hσ : ∀ a, σ (σ a) = a := cm_conj_conj hcm
  have horth : ∀ z, hA σ W.J (incM F H'.ι *ᵥ z) (incV F H'.x) = 0 := by
    intro z
    rw [hA_incM_incV]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 := (hH.orth (Pi.single j 1)).1
    rw [Matrix.mulVec_single_one] at h1
    rw [show (fun i => H'.ι i j) = H'.ι.col j from rfl, h1, map_zero, mul_zero]
  have h : Hyp σ W H' := ⟨hσ, hW.skew, by rw [hA_incV, hH.xx, map_zero], horth⟩
  set c : AE F E := algebraMap (AF F) (AE F E) t with hc_def
  have hcc : cA σ c = c := (cA σ).commutes t
  have hc : c - cA σ c = -hA σ W.J (incM F H'.ι *ᵥ (0 : Fin d₁ → AE F E)) (incM F H'.ι *ᵥ 0) := by
    rw [hcc, sub_self, Matrix.mulVec_zero, hA_zero_left, neg_zero]
  set z := elt h 0 c hc with hz
  have hmz : ∀ v, mat (z : UA σ W.J) *ᵥ v = v - hA σ W.J v (incV F H'.x) • (c • incV F H'.x) := by
    intro v
    rw [hz, mat_elt, nmat_mulVec, Matrix.mulVec_zero, hA_zero_right, zero_smul, sub_zero, zero_add]
  refine ⟨(z : UA σ W.J), z.2, fun u hu => ?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    show mat (z : UA σ W.J) * mat u = mat u * mat (z : UA σ W.J)
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmz, hmz, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_smul, unip_fix u hu]
    have e : hA σ W.J (mat u *ᵥ Pi.single i 1) (incV F H'.x) = hA σ W.J (Pi.single i 1) (incV F H'.x) :=
      calc hA σ W.J (mat u *ᵥ Pi.single i 1) (incV F H'.x)
          = hA σ W.J (mat u *ᵥ Pi.single i 1) (mat u *ᵥ incV F H'.x) := by rw [unip_fix u hu]
        _ = _ := hA_mat σ u _ _
    rw [e]
  · have hxy : hA σ W.J (incV F H'.x) (incV F H'.y) = 1 := by rw [hA_incV, hH.xy, map_one]
    have hyx : hA σ W.J (incV F H'.y) (incV F H'.x) = -1 := by
      have := hA_skew h.σσ h.skew (incV F H'.x) (incV F H'.y)
      rw [hxy, map_one] at this
      rw [← neg_neg (hA σ W.J (incV F H'.y) (incV F H'.x)), ← this]
    have hs : hA σ W.J (incV F H'.y - c • incV F H'.x) (incV F H'.x) = -1 := by
      rw [sub_eq_add_neg, hA_add_left, ← neg_smul,
        show hA σ W.J ((-c) • incV F H'.x) (incV F H'.x) = (-c) * hA σ W.J (incV F H'.x) (incV F H'.x) by
          simp [hA, smul_dotProduct],
        h.xx, mul_zero, add_zero, hyx]
    have hzy : mat (z : UA σ W.J) *ᵥ (incV F H'.y - c • incV F H'.x) = incV F H'.y := by
      rw [hmz, hs, neg_one_smul, sub_neg_eq_add, sub_add_cancel]
    calc mat (z : UA σ W.J)⁻¹ *ᵥ incV F H'.y
        = mat (z : UA σ W.J)⁻¹ *ᵥ (mat (z : UA σ W.J) *ᵥ (incV F H'.y - c • incV F H'.x)) := by rw [hzy]
      _ = incV F H'.y - c • incV F H'.x := by rw [Matrix.mulVec_mulVec, mat_inv_mul', Matrix.one_mulVec]

end GlobalTheory.UnipMass.CentralShift
