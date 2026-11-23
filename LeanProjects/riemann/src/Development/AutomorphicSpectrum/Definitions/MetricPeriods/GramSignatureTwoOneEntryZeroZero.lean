import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Model

open Matrix
open scoped ComplexOrder

theorem gramOf_one {N : ℕ} (hd : Fin N → ℝ) : gramOf hd 1 = diagonal (fun i => (hd i : ℂ)) := by
  simp [gramOf]

theorem inFlagDomain_one' (N j : ℕ) : InFlagDomain N j 1 := by
  refine ⟨by simp, ?_⟩
  have : -gramHead (sigForm N j) (N - j) (1 : Matrix (Fin N) (Fin N) ℂ) = 1 := by
    ext a b
    simp only [gramHead, gramOf_one, Matrix.neg_apply, submatrix_apply, diagonal_apply, Matrix.one_apply, sigForm]
    by_cases h : a = b
    · subst h; simp [a.2]
    · have : a.1 ≠ b.1 := fun e => h (Subtype.ext e)
      simp [h, this]
  rw [this]; exact PosDef.one

instance uniq1 : Unique {a : Fin 2 // (a : ℕ) < 1} where
  default := ⟨0, by simp⟩
  uniq := by rintro ⟨a, ha⟩; apply Subtype.ext; apply Fin.ext; simp only [Fin.val_zero]; omega

def eqv2 : {a : Fin 2 // (a : ℕ) < 2} ≃ Fin 2 := Equiv.subtypeUnivEquiv (fun a => a.2)

theorem det_head_one (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (gramHead hd 1 g).det = gramOf hd g 0 0 := by
  rw [det_unique]; rfl

theorem det_head_two (hd : Fin 2 → ℝ) (g : Matrix (Fin 2) (Fin 2) ℂ) :
    (gramHead hd 2 g).det = (gramOf hd g).det := by
  rw [← det_submatrix_equiv_self eqv2 (gramOf hd g)]; rfl

theorem det_head_zero {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) :
    (gramHead hd 0 g).det = 1 := by
  haveI : IsEmpty {a : Fin N // (a : ℕ) < 0} := ⟨fun a => by have := a.2; omega⟩
  exact det_isEmpty

theorem gram_signature_two_one_entry_zero_zero (z : ℂ) : gramOf (sigForm 2 1) !![1, 0; z, 1] 0 0 = -((1 - ‖z‖ ^ 2 : ℝ) : ℂ) := by
  simp [gramOf, sigForm, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, Complex.conj_mul']
  ring

theorem gram_signature_two_one_det (z : ℂ) : (gramOf (sigForm 2 1) !![1, 0; z, 1]).det = -1 := by
  simp [gramOf, sigForm, det_conjTranspose, det_fin_two_of, Fin.prod_univ_two]

theorem inFlagDomain_disc (z : ℂ) : InFlagDomain 2 1 !![1, 0; z, 1] ↔ ‖z‖ < 1 := by
  have h : -gramHead (sigForm 2 1) (2 - 1) !![1, 0; z, 1]
      = diagonal (fun _ : {a : Fin 2 // (a : ℕ) < 1} => ((1 - ‖z‖ ^ 2 : ℝ) : ℂ)) := by
    ext a b
    have ha : a = default := Subsingleton.elim (α := {a : Fin 2 // (a : ℕ) < 1}) _ _
    have hb : b = default := Subsingleton.elim (α := {a : Fin 2 // (a : ℕ) < 1}) _ _
    subst ha; rw [hb]
    rw [diagonal_apply_eq, Matrix.neg_apply]
    change -(gramOf (sigForm 2 1) !![1, 0; z, 1] 0 0) = _
    rw [gram_signature_two_one_entry_zero_zero, neg_neg]
  unfold InFlagDomain
  rw [h, posDef_diagonal_iff]
  have hu : IsUnit (!![1, 0; z, 1] : Matrix (Fin 2) (Fin 2) ℂ).det := by simp [det_fin_two_of]
  simp only [hu, true_and, Complex.zero_lt_real, forall_const]
  constructor
  · intro h; nlinarith [norm_nonneg z]
  · intro h; nlinarith [norm_nonneg z]

theorem stepPot_disc_zero (z : ℂ) (hz : ‖z‖ < 1) :
    stepPot 2 1 0 !![1, 0; z, 1] = -(1 / 2) * Real.log (1 - ‖z‖ ^ 2) := by
  have hp : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have : stepPot 2 1 0 !![1, 0; z, 1]
      = gramLog (sigForm 2 1) 2 !![1, 0; z, 1] - gramLog (sigForm 2 1) 1 !![1, 0; z, 1] := by
    simp [stepPot]
  rw [this, gramLog, gramLog, det_head_one, det_head_two, gram_signature_two_one_entry_zero_zero, gram_signature_two_one_det, norm_neg, norm_neg,
    Complex.norm_real, Real.norm_of_nonneg hp]
  simp

theorem stepPot_disc_one (z : ℂ) : stepPot 2 1 1 !![1, 0; z, 1] = 0 := by
  have : stepPot 2 1 1 !![1, 0; z, 1] = gramLog (sigForm 2 1) 2 !![1, 0; z, 1] := by
    simp [stepPot]
  rw [this, gramLog, det_head_two, gram_signature_two_one_det]
  simp

theorem stepPot_pos_zero (z : ℂ) :
    stepPot 2 2 0 !![1, 0; z, 1] = (1 / 2) * Real.log (1 + ‖z‖ ^ 2) := by
  have : stepPot 2 2 0 !![1, 0; z, 1]
      = gramLog (sigForm 2 2) 1 !![1, 0; z, 1] - gramLog (sigForm 2 2) 0 !![1, 0; z, 1] := by
    simp [stepPot]
  have h : gramOf (sigForm 2 2) !![1, 0; z, 1] 0 0 = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := by
    simp [gramOf, sigForm, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, Complex.conj_mul']
  rw [this, gramLog, gramLog, det_head_one, det_head_zero, h, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]
  simp

theorem stepPot_neg_zero (z : ℂ) :
    stepPot 2 0 0 !![1, 0; z, 1] = (1 / 2) * Real.log (1 + ‖z‖ ^ 2) := by
  have : stepPot 2 0 0 !![1, 0; z, 1] = gramLog (sigForm 2 0) 1 !![1, 0; z, 1] := by
    simp [stepPot]
  have h : gramOf (sigForm 2 0) !![1, 0; z, 1] 0 0 = -((1 + ‖z‖ ^ 2 : ℝ) : ℂ) := by
    simp [gramOf, sigForm, Matrix.mul_apply, Fin.sum_univ_two, diagonal_apply, Complex.conj_mul']
    ring
  rw [this, gramLog, det_head_one, h, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

theorem hermitian_two_form_eq (G : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) :
    herm2 G ![1, a] ![1, b] = G 0 0 + G 0 1 * b + (starRingEnd ℂ a) * (G 1 0 + G 1 1 * b) := by
  simp [herm2, dotProduct, mulVec, Fin.sum_univ_two]

theorem xiPot_one (a : ℂ) : xiPot 1 a = -Real.log (1 + ‖a‖ ^ 2) := by
  have : herm2 1 ![1, a] ![1, a] = ((1 + ‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [hermitian_two_form_eq]; simp [Complex.conj_mul']
  rw [xiPot, this, Complex.ofReal_re]; simp

theorem hermitian_two_form_re_pos {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) (a : ℂ) :
    0 < (herm2 G ![1, a] ![1, a]).re := by
  have := hG.dotProduct_mulVec_pos (x := ![1, a]) (by intro h; simpa using congrFun h 0)
  exact (Complex.lt_def.mp this).1

theorem logSin_eq {G : Matrix (Fin 2) (Fin 2) ℂ} (hG : G.PosDef) {a b : ℂ} (hab : a ≠ b) :
    logSin G a b = Real.log ‖a - b‖ + (xiPot G a + xiPot G b) / 2 := by
  have ha := hermitian_two_form_re_pos hG a
  have hb := hermitian_two_form_re_pos hG b
  have hd : 0 < G.det.re := (Complex.lt_def.mp hG.det_pos).1
  have h10 : G 1 0 = starRingEnd ℂ (G 0 1) := (hG.1.apply 1 0).symm
  have h00 : (G 0 0).im = 0 := Complex.conj_eq_iff_im.mp (hG.1.apply 0 0)
  have h11 : (G 1 1).im = 0 := Complex.conj_eq_iff_im.mp (hG.1.apply 1 1)
  have key : (herm2 G ![1, a] ![1, a]).re * (herm2 G ![1, b] ![1, b]).re - ‖herm2 G ![1, a] ![1, b]‖ ^ 2
      = ‖a - b‖ ^ 2 * G.det.re := by
    rw [Complex.sq_norm, Complex.sq_norm, det_fin_two]
    simp only [hermitian_two_form_eq, h10, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im, h00, h11]
    ring
  have hn : 0 < ‖a - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hab)
  have e : 1 - ‖herm2 G ![1, a] ![1, b]‖ ^ 2 /
      ((herm2 G ![1, a] ![1, a]).re * (herm2 G ![1, b] ![1, b]).re)
      = ‖a - b‖ ^ 2 * G.det.re / ((herm2 G ![1, a] ![1, a]).re * (herm2 G ![1, b] ![1, b]).re) := by
    rw [← key]; field_simp
  rw [logSin, e, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) hd.ne',
    Real.log_mul ha.ne' hb.ne', Real.log_pow, xiPot, xiPot]
  push_cast; ring

theorem det_gramHead_ne_zero {N j k : ℕ} {g : Matrix (Fin N) (Fin N) ℂ} (hg : InFlagDomain N j g)
    (hk : k ≤ N - j) : (gramHead (sigForm N j) k g).det ≠ 0 := by
  let e : {a : Fin N // (a : ℕ) < k} → {a : Fin N // (a : ℕ) < N - j} := fun a => ⟨a.1, lt_of_lt_of_le a.2 hk⟩
  have he : Function.Injective e := fun a b h => Subtype.ext (congrArg Subtype.val h : (e a).1 = (e b).1)
  have h1 : (-gramHead (sigForm N j) k g).PosDef := by
    have h0 : -gramHead (sigForm N j) k g = (-gramHead (sigForm N j) (N - j) g).submatrix e e := by
      ext a b; simp only [gramHead, Matrix.neg_apply, submatrix_apply, e]
    rw [h0]; exact Matrix.PosDef.submatrix hg.2 he
  have h2 := h1.det_pos.ne'
  rw [det_neg] at h2
  exact right_ne_zero_of_mul h2

theorem gramLog_top (N j : ℕ) (g : Matrix (Fin N) (Fin N) ℂ) :
    gramLog (sigForm N j) N g = Real.log ‖g.det‖ := by
  have h : (gramHead (sigForm N j) N g).det = (gramOf (sigForm N j) g).det := by
    rw [← det_submatrix_equiv_self (Equiv.subtypeUnivEquiv (p := fun a : Fin N => (a : ℕ) < N) (fun a => a.2))
      (gramOf (sigForm N j) g)]; rfl
  have h2 : ‖∏ i : Fin N, ((sigForm N j i : ℝ) : ℂ)‖ = 1 := by
    rw [norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    unfold sigForm; split_ifs <;> simp
  rw [gramLog, h, gramOf, det_mul, det_mul, det_diagonal, det_conjTranspose, norm_mul, norm_mul, h2, norm_star,
    mul_one, ← sq, Real.log_pow]
  push_cast; ring

end GlobalTheory.CompanionTheory.Ar.PB.Model
