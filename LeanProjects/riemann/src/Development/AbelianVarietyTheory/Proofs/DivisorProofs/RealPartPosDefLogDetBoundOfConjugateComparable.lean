import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReLePowMulDetReStatement
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.RealPartDet

open Matrix

theorem quad_eq_sum {ι : Type} [Fintype ι] (G : Matrix ι ι ℂ) (c : ι → ℂ) :
    star c ⬝ᵥ G *ᵥ c = ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * G i j := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem quad_transpose_eq_sum {ι : Type} [Fintype ι] (G : Matrix ι ι ℂ) (c : ι → ℂ) :
    star c ⬝ᵥ Gᵀ *ᵥ c = ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * G i j := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Complex.star_def, transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem map_re_map_ofReal {ι : Type} [Fintype ι] {G : Matrix ι ι ℂ} (hG : G.IsHermitian) :
    (G.map Complex.re).map (fun r : ℝ => (r : ℂ)) = (2 : ℂ)⁻¹ • (G + Gᵀ) := by
  ext i j
  have h := hG.apply j i
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, transpose_apply, smul_eq_mul, ← h,
    Complex.star_def, Complex.re_eq_add_conj]
  ring

theorem quad_half_re {ι : Type} [Fintype ι] (G : Matrix ι ι ℂ) (c : ι → ℂ) :
    (star c ⬝ᵥ ((2 : ℂ)⁻¹ • (G + Gᵀ)) *ᵥ c).re
      = ((star c ⬝ᵥ G *ᵥ c).re + (star c ⬝ᵥ Gᵀ *ᵥ c).re) / 2 := by
  rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.add_mulVec, dotProduct_add, smul_eq_mul]
  simp [Complex.mul_re]
  ring

theorem quad_ofReal {ι : Type} [Fintype ι] (A : Matrix ι ι ℝ) (x : ι → ℝ) :
    star (fun i => (x i : ℂ)) ⬝ᵥ (A.map (fun r : ℝ => (r : ℂ))) *ᵥ (fun i => (x i : ℂ))
      = ((x ⬝ᵥ A *ᵥ x : ℝ) : ℂ) := by
  simp [dotProduct, mulVec, Complex.ofReal_sum, Complex.ofReal_mul]

theorem main : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (κ : ℝ), G.PosDef → 1 ≤ κ →
    (∀ c : ι → ℂ, (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * G i j).re ≤
      κ * (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * G i j).re) →
    (G.map Complex.re).PosDef ∧
      |Real.log (G.map Complex.re).det - Real.log G.det.re| ≤ Fintype.card ι * Real.log (2 * κ) := by
  intro ι _ _ G κ hG hκ h
  set A := G.map Complex.re with hAdef
  set Ac := A.map (fun r : ℝ => (r : ℂ)) with hAcdef
  have hAc : Ac = (2 : ℂ)⁻¹ • (G + Gᵀ) := map_re_map_ofReal hG.isHermitian
  have h2 : (0 : ℂ) < (2 : ℂ)⁻¹ := by rw [Complex.pos_iff]; norm_num
  have hAcpd : Ac.PosDef := by rw [hAc]; exact (hG.add hG.transpose).smul h2

  have hq1 : ∀ c : ι → ℂ, (star c ⬝ᵥ G *ᵥ c).re ≤ κ * (star c ⬝ᵥ Gᵀ *ᵥ c).re := by
    intro c; rw [quad_eq_sum, quad_transpose_eq_sum]; exact h c
  have hq2 : ∀ c : ι → ℂ, (star c ⬝ᵥ Gᵀ *ᵥ c).re ≤ κ * (star c ⬝ᵥ G *ᵥ c).re := by
    intro c
    have := h (fun i => (starRingEnd ℂ) (c i))
    simp only [Complex.conj_conj] at this
    rw [quad_transpose_eq_sum, quad_eq_sum]
    exact this
  have hn1 : ∀ c : ι → ℂ, 0 ≤ (star c ⬝ᵥ G *ᵥ c).re := fun c =>
    (Complex.nonneg_iff.1 (hG.posSemidef.dotProduct_mulVec_nonneg c)).1
  have hn2 : ∀ c : ι → ℂ, 0 ≤ (star c ⬝ᵥ Gᵀ *ᵥ c).re := fun c =>
    (Complex.nonneg_iff.1 (hG.transpose.posSemidef.dotProduct_mulVec_nonneg c)).1
  have hqA : ∀ c : ι → ℂ, (star c ⬝ᵥ Ac *ᵥ c).re
      = ((star c ⬝ᵥ G *ᵥ c).re + (star c ⬝ᵥ Gᵀ *ᵥ c).re) / 2 := fun c => by
    rw [hAc]; exact quad_half_re G c

  have hApd : A.PosDef := by
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨?_, fun x hx => ?_⟩
    · ext i j
      have e := hG.isHermitian.apply i j
      simp only [conjTranspose_apply, star_trivial, hAdef, Matrix.map_apply]
      rw [← e, Complex.star_def, Complex.conj_re]
    · have hc : (fun i => (x i : ℂ)) ≠ 0 := by
        intro h0; apply hx; funext i
        have := congrFun h0 i
        simpa using this
      have := (posDef_iff_dotProduct_mulVec.1 hAcpd).2 hc
      rw [quad_ofReal] at this
      simpa [star_trivial] using (Complex.zero_lt_real.1 this)
  refine ⟨hApd, ?_⟩

  have hdet : Ac.det.re = A.det := by
    have := (Complex.ofRealHom.map_det A)
    rw [hAcdef]
    rw [show A.map (fun r : ℝ => (r : ℂ)) = Complex.ofRealHom.mapMatrix A from rfl, ← this]
    simp
  have d1 : G.det.re ≤ 2 ^ Fintype.card ι * A.det := by
    rw [← hdet]
    refine GlobalTheory.T.det_re_le_pow_mul_det_re_of_posDef ι G Ac 2 hG hAcpd fun c => ?_
    rw [hqA c]; linarith [hn2 c]
  have d2 : A.det ≤ κ ^ Fintype.card ι * G.det.re := by
    rw [← hdet]
    refine GlobalTheory.T.det_re_le_pow_mul_det_re_of_posDef ι Ac G κ hAcpd hG fun c => ?_
    rw [hqA c]; nlinarith [hq2 c, hn1 c]
  have ha : 0 < A.det := hApd.det_pos
  have hg : 0 < G.det.re := (Complex.pos_iff.1 hG.det_pos).1
  have hκ0 : 0 < κ := by linarith
  have l1 : Real.log G.det.re ≤ Fintype.card ι * Real.log 2 + Real.log A.det := by
    have := Real.log_le_log hg d1
    rwa [Real.log_mul (by positivity) ha.ne', Real.log_pow] at this
  have l2 : Real.log A.det ≤ Fintype.card ι * Real.log κ + Real.log G.det.re := by
    have := Real.log_le_log ha d2
    rwa [Real.log_mul (by positivity) hg.ne', Real.log_pow] at this
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlk : 0 ≤ Real.log κ := Real.log_nonneg hκ
  have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  rw [Real.log_mul (by norm_num) hκ0.ne', mul_add]
  rw [abs_sub_le_iff]
  constructor
  · nlinarith [mul_nonneg hn hl2]
  · nlinarith [mul_nonneg hn hlk]

end GlobalTheory.RealPartDet
