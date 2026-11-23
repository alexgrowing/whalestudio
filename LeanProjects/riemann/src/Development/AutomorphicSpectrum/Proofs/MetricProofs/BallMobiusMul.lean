import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct

variable {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem ballMat_ballPt (q : Ψ × Fin j × Fin j' ≃ Fin n) (W : Ψ → Matrix (Fin j') (Fin j) ℂ) (τ : Ψ) :
    ballMat q (ballPt q W) τ = (W τ)ᵀ := by
  ext a b
  simp [ballMat, ballPt]

theorem sgI_form (a : Fin j → ℂ) (b : Fin j' → ℂ) :
    star (Sum.elim a b : Sg j j' → ℂ) ⬝ᵥ (sgI j j' *ᵥ Sum.elim a b) = star a ⬝ᵥ a - star b ⬝ᵥ b := by
  simp [sgI, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type, Function.comp_def, sub_eq_add_neg,
    neg_mulVec, Finset.sum_neg_distrib]

theorem form_mulVec {v : Matrix (Sg j j') (Sg j j') ℂ} (hv : IsSgU v) (z : Sg j j' → ℂ) :
    star (v *ᵥ z) ⬝ᵥ (sgI j j' *ᵥ (v *ᵥ z)) = star z ⬝ᵥ (sgI j j' *ᵥ z) := by
  have hv' : vᴴ * sgI j j' * v = sgI j j' := hv
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hv']

theorem norm_lt_of_ball {W : Matrix (Fin j') (Fin j) ℂ} (hW : (1 - (Wᵀ)ᴴ * Wᵀ).PosDef) {y : Fin j' → ℂ}
    (hy : y ≠ 0) : (star (Wᴴ *ᵥ y) ⬝ᵥ (Wᴴ *ᵥ y)).re < (star y ⬝ᵥ y).re := by
  have hc : star y ≠ 0 := by simpa using hy
  have h := hW.dotProduct_mulVec_pos hc
  have hw : Wᵀ *ᵥ star y = star (Wᴴ *ᵥ y) := by
    rw [star_mulVec, conjTranspose_conjTranspose, mulVec_transpose]
  have e : star (star y) ⬝ᵥ ((1 - (Wᵀ)ᴴ * Wᵀ) *ᵥ star y) =
      star y ⬝ᵥ y - star (Wᴴ *ᵥ y) ⬝ᵥ (Wᴴ *ᵥ y) := by
    rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hw, dotProduct_sub, star_star, dotProduct_comm y (star y)]
    congr 1
    rw [dotProduct_mulVec, vecMul_conjTranspose, hw, star_star, dotProduct_comm]
  rw [e] at h
  have := (Complex.lt_def.1 h).1
  simpa using this

theorem isUnit_det_P {v : Matrix (Sg j j') (Sg j j') ℂ} (hv : IsSgU v) {W : Matrix (Fin j') (Fin j) ℂ}
    (hW : (1 - (Wᵀ)ᴴ * Wᵀ).PosDef) : IsUnit (v.toBlocks₁₁ + v.toBlocks₁₂ * W).det := by
  by_contra hne
  have h0 : (v.toBlocks₁₁ + v.toBlocks₁₂ * W).det = 0 := by simpa using hne
  obtain ⟨x, hx, hPx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hz : v *ᵥ Sum.elim x (W *ᵥ x) =
      Sum.elim (0 : Fin j → ℂ) ((v.toBlocks₂₁ + v.toBlocks₂₂ * W) *ᵥ x) := by
    conv_lhs => rw [← fromBlocks_toBlocks v]
    rw [fromBlocks_mulVec]
    have h1 : v.toBlocks₁₁ *ᵥ x + v.toBlocks₁₂ *ᵥ (W *ᵥ x) = 0 := by
      rw [← hPx, add_mulVec, mulVec_mulVec]
    show Sum.elim (v.toBlocks₁₁ *ᵥ x + v.toBlocks₁₂ *ᵥ (W *ᵥ x))
      (v.toBlocks₂₁ *ᵥ x + v.toBlocks₂₂ *ᵥ (W *ᵥ x)) = _
    rw [h1, add_mulVec, mulVec_mulVec]
  have hen := form_mulVec hv (Sum.elim x (W *ᵥ x))
  rw [hz, sgI_form, sgI_form] at hen
  set y := W *ᵥ x with hy
  set Qx := (v.toBlocks₂₁ + v.toBlocks₂₂ * W) *ᵥ x
  have hxx : 0 < (star x ⬝ᵥ x).re := by
    have := (Complex.lt_def.1 (dotProduct_star_self_pos_iff.2 hx)).1
    simpa using this
  have hQ : 0 ≤ (star Qx ⬝ᵥ Qx).re := (Complex.le_def.1 (dotProduct_star_self_nonneg Qx)).1
  have hre := congrArg Complex.re hen
  simp only [Complex.sub_re, star_zero, dotProduct_zero, Complex.zero_re] at hre
  have hyy : (star x ⬝ᵥ x).re ≤ (star y ⬝ᵥ y).re := by linarith
  have hy0 : y ≠ 0 := by
    intro h
    rw [h] at hyy
    simp at hyy
    linarith
  have hlt := norm_lt_of_ball hW hy0
  set w := Wᴴ *ᵥ y with hw
  have hnn : 0 ≤ (star (x - w) ⬝ᵥ (x - w)).re :=
    (Complex.le_def.1 (dotProduct_star_self_nonneg (x - w))).1
  have h1 : star x ⬝ᵥ w = star y ⬝ᵥ y := by
    rw [hw, dotProduct_mulVec, hy, star_mulVec]
  have h2 : star w ⬝ᵥ x = star y ⬝ᵥ y := by
    rw [hw, star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
  have hexp : star (x - w) ⬝ᵥ (x - w) = star x ⬝ᵥ x - star x ⬝ᵥ w - star w ⬝ᵥ x + star w ⬝ᵥ w := by
    simp only [star_sub, sub_dotProduct, dotProduct_sub]
    ring
  rw [hexp, h1, h2] at hnn
  simp only [Complex.add_re, Complex.sub_re] at hnn
  linarith

theorem moebW_mul (u v : Matrix (Sg j j') (Sg j j') ℂ) (W : Matrix (Fin j') (Fin j) ℂ)
    (hP : IsUnit (v.toBlocks₁₁ + v.toBlocks₁₂ * W).det) :
    moebW (u * v) W = moebW u (moebW v W) := by
  set P := v.toBlocks₁₁ + v.toBlocks₁₂ * W with hPd
  set Q := v.toBlocks₂₁ + v.toBlocks₂₂ * W with hQd
  have hPP : P⁻¹ * P = 1 := nonsing_inv_mul _ hP
  have hPP' : P * P⁻¹ = 1 := mul_nonsing_inv _ hP
  have hv : moebW v W = Q * P⁻¹ := rfl
  have huv : u * v = fromBlocks
      (u.toBlocks₁₁ * v.toBlocks₁₁ + u.toBlocks₁₂ * v.toBlocks₂₁)
      (u.toBlocks₁₁ * v.toBlocks₁₂ + u.toBlocks₁₂ * v.toBlocks₂₂)
      (u.toBlocks₂₁ * v.toBlocks₁₁ + u.toBlocks₂₂ * v.toBlocks₂₁)
      (u.toBlocks₂₁ * v.toBlocks₁₂ + u.toBlocks₂₂ * v.toBlocks₂₂) := by
    rw [← fromBlocks_multiply, fromBlocks_toBlocks, fromBlocks_toBlocks]
  have e1 : (u * v).toBlocks₁₁ + (u * v).toBlocks₁₂ * W =
      (u.toBlocks₁₁ + u.toBlocks₁₂ * (Q * P⁻¹)) * P := by
    have hr : (u.toBlocks₁₁ + u.toBlocks₁₂ * (Q * P⁻¹)) * P = u.toBlocks₁₁ * P + u.toBlocks₁₂ * Q := by
      rw [Matrix.add_mul, Matrix.mul_assoc u.toBlocks₁₂, Matrix.mul_assoc Q, hPP, Matrix.mul_one]
    rw [hr, huv, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, hPd, hQd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  have e2 : (u * v).toBlocks₂₁ + (u * v).toBlocks₂₂ * W =
      (u.toBlocks₂₁ + u.toBlocks₂₂ * (Q * P⁻¹)) * P := by
    have hr : (u.toBlocks₂₁ + u.toBlocks₂₂ * (Q * P⁻¹)) * P = u.toBlocks₂₁ * P + u.toBlocks₂₂ * Q := by
      rw [Matrix.add_mul, Matrix.mul_assoc u.toBlocks₂₂, Matrix.mul_assoc Q, hPP, Matrix.mul_one]
    rw [hr, huv, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, hPd, hQd]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [hv]
  unfold moebW
  rw [e1, e2, Matrix.mul_inv_rev, Matrix.mul_assoc, ← Matrix.mul_assoc P, hPP', Matrix.one_mul]

theorem moebBall_mul : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → ∀ t ∈ ballDom q, moebBall q (fun τ => u τ * v τ) t = moebBall q u (moebBall q v t) := by
  intro Ψ _ j j' n q u v hu hv t ht
  unfold moebBall
  congr 1
  funext τ
  rw [ballMat_ballPt, transpose_transpose]
  refine moebW_mul _ _ _ (isUnit_det_P (hv τ) ?_)
  simpa using ht τ

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct
