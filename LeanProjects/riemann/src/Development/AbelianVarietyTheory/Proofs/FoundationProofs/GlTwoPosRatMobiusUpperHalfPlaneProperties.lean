import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNMob

theorem det_pos (g : GQ) : 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 := by
  have h := (Matrix.mem_glpos (g : GL (Fin 2) ℚ)).1 g.2
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h
  simpa [ent] using h

theorem im_frac (a b c d : ℝ) (z : ℂ) :
    (((a : ℂ) * z + b) / ((c : ℂ) * z + d)).im = (a * d - b * c) * z.im / Complex.normSq ((c : ℂ) * z + d) := by
  rw [Complex.div_im]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem denom_ne (g : GQ) {z : ℂ} (hz : z ∈ Hs) : (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  have hr := congrArg Complex.re h
  simp at hi hr
  have hz' : 0 < z.im := hz
  have hc : ent g 1 0 = 0 := by
    rcases hi with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hz'.ne'
  rw [hc] at hr
  have hd : ent g 1 1 = 0 := by simpa using hr
  have := det_pos g
  rw [hc, hd] at this
  simp at this

theorem mob_mem (g : GQ) {z : ℂ} (hz : z ∈ Hs) : mob g z ∈ Hs := by
  have hne := denom_ne g hz
  have e : mob g z = ((((ent g 0 0 : ℝ)) : ℂ) * z + ((ent g 0 1 : ℝ) : ℂ)) /
      ((((ent g 1 0 : ℝ)) : ℂ) * z + ((ent g 1 1 : ℝ) : ℂ)) := by
    simp [mob]
  show 0 < (mob g z).im
  rw [e, im_frac]
  have hn : 0 < Complex.normSq ((((ent g 1 0 : ℝ)) : ℂ) * z + ((ent g 1 1 : ℝ) : ℂ)) := by
    rw [Complex.normSq_pos]; simpa using hne
  have hd : (0 : ℝ) < (ent g 0 0 : ℝ) * (ent g 1 1 : ℝ) - (ent g 0 1 : ℝ) * (ent g 1 0 : ℝ) := by
    exact_mod_cast det_pos g
  have hz' : 0 < z.im := hz
  positivity

theorem ent_mul (g h : GQ) (i j : Fin 2) : ent (g * h) i j = ent g i 0 * ent h 0 j + ent g i 1 * ent h 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

theorem frac_comp (a b c d N D : ℂ) (hD : D ≠ 0) :
    (a * (N / D) + b) / (c * (N / D) + d) = (a * N + b * D) / (c * N + d * D) := by
  rw [show a * (N / D) + b = (a * N + b * D) / D by field_simp,
    show c * (N / D) + d = (c * N + d * D) / D by field_simp, div_div_div_cancel_right₀ hD]

theorem mob_mul (g h : GQ) {z : ℂ} (hz : z ∈ Hs) : mob (g * h) z = mob g (mob h z) := by
  have hne := denom_ne h hz
  simp only [mob, ent_mul]
  push_cast
  rw [frac_comp _ _ _ _ _ _ hne]
  congr 1 <;> ring

theorem mob_one (z : ℂ) : mob 1 z = z := by simp [mob, ent]

theorem mob_ofSL (γ : SL(2, ℤ)) (τ : ℍ) : mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [mob, ent, ofSL]

theorem mob_diff (g : GQ) : DifferentiableOn ℂ (mob g) Hs := by
  intro z hz
  have hne := denom_ne g hz
  show DifferentiableWithinAt ℂ (fun z : ℂ => ((ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) /
    ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))) Hs z
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) z := by fun_prop
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ)) z := by fun_prop
  exact (h1.div h2 hne).differentiableWithinAt

theorem mob_upper (g : GQ) (hc : ent g 1 0 = 0) : 0 < ent g 0 0 / ent g 1 1 ∧
    ∀ z : ℂ, mob g z = ((ent g 0 0 / ent g 1 1 : ℚ) : ℂ) * z + ((ent g 0 1 / ent g 1 1 : ℚ) : ℂ) := by
  have hdet := det_pos g
  rw [hc, mul_zero, sub_zero] at hdet
  have hd : ent g 1 1 ≠ 0 := by rintro h; rw [h, mul_zero] at hdet; exact lt_irrefl _ hdet
  refine ⟨?_, fun z => ?_⟩
  · have : ent g 0 0 / ent g 1 1 = ent g 0 0 * ent g 1 1 / (ent g 1 1 * ent g 1 1) := by
      field_simp
    rw [this]; exact div_pos hdet (mul_self_pos.2 hd)
  · have hd' : (ent g 1 1 : ℂ) ≠ 0 := by exact_mod_cast hd
    simp only [mob, hc]
    push_cast
    simp only [zero_mul, zero_add]
    rw [add_div, mul_div_right_comm]

end GlobalTheory.FNMob

theorem GlobalTheory.FN.mob_props : (∀ (g : GQ) (z : ℂ), z ∈ Hs → mob g z ∈ Hs) ∧ (∀ (g h : GQ) (z : ℂ), z ∈ Hs → mob (g * h) z = mob g (mob h z)) ∧ (∀ z : ℂ, mob 1 z = z) ∧ (∀ (γ : SL(2, ℤ)) (τ : ℍ), mob (ofSL γ) τ = ((γ • τ : ℍ) : ℂ)) ∧ (∀ g : GQ, DifferentiableOn ℂ (mob g) Hs) ∧ ∀ g : GQ, ent g 1 0 = 0 → 0 < ent g 0 0 / ent g 1 1 ∧ ∀ z : ℂ, mob g z = ((ent g 0 0 / ent g 1 1 : ℚ) : ℂ) * z + ((ent g 0 1 / ent g 1 1 : ℚ) : ℂ) :=
  ⟨fun g _ hz => GlobalTheory.FNMob.mob_mem g hz, fun g h _ hz => GlobalTheory.FNMob.mob_mul g h hz, GlobalTheory.FNMob.mob_one,
    GlobalTheory.FNMob.mob_ofSL, GlobalTheory.FNMob.mob_diff, GlobalTheory.FNMob.mob_upper⟩
