import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.MobLaws

theorem det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := g.2
  rw [Matrix.mem_glpos] at h
  simpa [ent, Matrix.det_fin_two] using h

theorem ent_mul (g h : GQ) (i j : Fin 2) : ent (g * h) i j = ent g i 0 * ent h 0 j + ent g i 1 * ent h 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

theorem den_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h0
  have hy : 0 < z.im := hz
  have him := congrArg Complex.im h0
  have hre := congrArg Complex.re h0
  simp at him hre
  have hd := det_pos g
  rcases him with hc | hc
  · rw [hc] at hre hd; simp at hre; rw [hre] at hd; simp at hd
  · linarith

theorem im_mob (g : GQ) (z : ℂ) : (mob g z).im =
    (ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) * z.im /
      Complex.normSq ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) := by
  rw [mob, Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ratCast_re, Complex.ratCast_im]
  push_cast
  rw [div_sub_div_same]
  congr 1
  ring

theorem mob_mem (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  show 0 < (mob g z).im
  rw [im_mob]
  have hy : 0 < z.im := hz
  have hd : (0:ℝ) < ((ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 : ℚ) : ℝ) := by exact_mod_cast det_pos g
  exact div_pos (mul_pos hd hy) (Complex.normSq_pos.2 (den_ne g hz))

theorem complex_mobius_fraction_clear_denom (a b c d N D : ℂ) (hD : D ≠ 0) :
    (a * (N / D) + b) / (c * (N / D) + d) = (a * N + b * D) / (c * N + d * D) := by
  have e1 : a * (N / D) + b = (a * N + b * D) / D := by field_simp
  have e2 : c * (N / D) + d = (c * N + d * D) / D := by field_simp
  rw [e1, e2, div_div_div_cancel_right₀ hD]

theorem mob_mul (g h : GQ) {z : ℂ} (hz : z ∈ Hs) : mob (g * h) z = mob g (mob h z) := by
  have h1 := den_ne h hz
  unfold mob
  rw [complex_mobius_fraction_clear_denom _ _ _ _ _ _ h1]
  simp only [ent_mul]
  push_cast
  congr 1 <;> ring

theorem mob_one (z : ℂ) : mob 1 z = z := by
  simp [mob, ent]

theorem mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold mob
  exact ((differentiableAt_id.const_mul _).add_const _).div
    ((differentiableAt_id.const_mul _).add_const _) (den_ne g hz)

theorem toGQ_SL (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  have h : (0 : ℤ) < (γ : Matrix (Fin 2) (Fin 2) ℤ).det := by rw [γ.2]; norm_num
  apply Subtype.ext; apply Units.ext; ext i j
  simp [toGQ, h, ofSL]

theorem toGQ_mul (m m' : Matrix (Fin 2) (Fin 2) ℤ) (hm : 0 < m.det) (hm' : 0 < m'.det) :
    toGQ (m * m') = toGQ m * toGQ m' := by
  have h : 0 < (m * m').det := by rw [Matrix.det_mul]; exact mul_pos hm hm'
  apply Subtype.ext; apply Units.ext
  simp only [toGQ, h, hm, hm', dif_pos]
  ext i j
  simp [Matrix.mul_apply]

end GlobalTheory.KZ.MobLaws

namespace GlobalTheory.KZ

theorem mob_laws : (∀ (g : GQ), ∀ z ∈ Hs, mob g z ∈ Hs) ∧ (∀ (g h : GQ), ∀ z ∈ Hs, mob (g * h) z = mob g (mob h z)) ∧ (∀ z, mob 1 z = z) ∧ (∀ g : GQ, DifferentiableOn ℂ (mob g) Hs) ∧ (∀ γ : SL(2, ℤ), toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ) ∧ (∀ m m' : Matrix (Fin 2) (Fin 2) ℤ, 0 < m.det → 0 < m'.det → toGQ (m * m') = toGQ m * toGQ m') :=
  ⟨fun g _ hz => MobLaws.mob_mem g hz, fun g h _ hz => MobLaws.mob_mul g h hz, MobLaws.mob_one,
    MobLaws.mob_diff, MobLaws.toGQ_SL, MobLaws.toGQ_mul⟩

end GlobalTheory.KZ
