import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusHomeo

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

section Mat

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} {a : ι → ℂ}

theorem heisMat_conj_scale {g : Matrix ι ι ℂ} (hg : gᴴ * H * g = H) {α : ℂ}
    (hga : g *ᵥ a = α • a) {y : ι → ℂ} (hgy : g *ᵥ y = y) (s : ℂ) :
    g * heisMat H a y s =
      heisMat H a (starRingEnd ℂ α • y) ((Complex.normSq α : ℂ) * s) * g := by
  refine matrix_ext_mulVec fun z => ?_
  have h1 : hForm H a z = starRingEnd ℂ α * hForm H a (g *ᵥ z) := by
    rw [← hForm_mulVec_of_unitary H hg a z, hga, hForm_smul_left]
  have h2 : hForm H y z = hForm H y (g *ᵥ z) := by
    conv_lhs => rw [← hForm_mulVec_of_unitary H hg y z, hgy]
  rw [← mulVec_mulVec, ← mulVec_mulVec, heisMat_mulVec, heisMat_mulVec, h1, h2, hForm_smul_left,
    Complex.conj_conj, Complex.normSq_eq_conj_mul_self]
  simp only [mulVec_add, mulVec_sub, mulVec_smul, hga, hgy]
  module

omit [DecidableEq ι] in

theorem heisS_conj_smul (α : ℂ) (y : ι → ℂ) (t : ℝ) :
    heisS H (starRingEnd ℂ α • y) (Complex.normSq α * t) = (Complex.normSq α : ℂ) * heisS H y t := by
  have e : hForm H (starRingEnd ℂ α • y) (starRingEnd ℂ α • y) =
      (Complex.normSq α : ℂ) * hForm H y y := by
    rw [hForm_smul_left, hForm_smul_right, Complex.conj_conj, Complex.normSq_eq_conj_mul_self]
    ring
  apply Complex.ext
  · simp only [heisS, e, Complex.re_ofReal_mul]
    ring
  · simp only [heisS, Complex.im_ofReal_mul]

end Mat

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W}

def heisScale (h : HermitianForm F E W) (v : Basis ι E W) (x₀ w₀ : W) (c : InfinitePlace E → ℂ) :
    heisY h v x₀ w₀ →ₗ[ℝ] heisY h v x₀ w₀ where
  toFun y := ⟨fun w => c w • (y : InfinitePlace E → ι → ℂ) w, mem_heisY.2 fun w => by
    simp only [hForm_smul_right, (y.2 w).1, (y.2 w).2, mul_zero, and_self]⟩
  map_add' y z := by
    apply Subtype.ext
    funext w
    simp [smul_add]
  map_smul' r y := by
    apply Subtype.ext
    funext w
    change c w • ((r • (y : InfinitePlace E → ι → ℂ)) w) =
      r • (c w • (y : InfinitePlace E → ι → ℂ) w)
    rw [Pi.smul_apply, real_smul_vec, real_smul_vec, smul_comm]

theorem heisPoint_torus (hp : IsHyperbolicPair h x₀ w₀) (g : archUnitary h v)
    (α : InfinitePlace E → ℂ)
    (hga : ∀ w, ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      α w • vecAt v x₀ w)
    (hgy : ∀ w (z : ι → ℂ), star (vecAt v x₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      star (vecAt v w₀ w) ⬝ᵥ (gramAt h v w *ᵥ z) = 0 →
      ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z = z)
    (p : HeisCoord h v x₀ w₀) :
    g * ((heisPoint hp p : unipRadical h v x₀) : archUnitary h v) * g⁻¹ =
      heisPoint hp (heisScale h v x₀ w₀ (fun w => starRingEnd ℂ (α w)) p.1,
        fun w => Complex.normSq (α w) * p.2 w) := by
  apply Subtype.ext
  funext w
  apply Units.ext
  have hu := archUnitary_at_place g w
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply, Units.val_mul]
  rw [heisPoint_val, heisPoint_val, heisMatAt, heisMatAt,
    heisMat_conj_scale hu (hga w) (hgy w _ (p.1.2 w).1 (p.1.2 w).2), mul_assoc, Units.mul_inv,
    mul_one]
  congr 1
  exact (heisS_conj_smul (α w) _ (p.2 w)).symm

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
