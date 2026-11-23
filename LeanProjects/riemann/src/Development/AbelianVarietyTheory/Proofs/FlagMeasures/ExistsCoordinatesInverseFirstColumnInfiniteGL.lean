import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingCons
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralPiProdTwo
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

noncomputable section

namespace GlobalTheory.FirstColumnCoord

variable {k : ℕ}

def blk (h : Matrix (Fin k) (Fin k) ℂ) (R : Fin k → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.of (Fin.cons (Fin.cons 1 R) (fun a' => Fin.cons 0 (h a')) : Fin (k + 1) → Fin (k + 1) → ℂ)

@[simp] theorem firstColumnBlockMatrix_apply_zero_zero (h : Matrix (Fin k) (Fin k) ℂ) (R : Fin k → ℂ) : blk h R 0 0 = 1 := rfl
@[simp] theorem blk_zs (h : Matrix (Fin k) (Fin k) ℂ) (R : Fin k → ℂ) (b) : blk h R 0 b.succ = R b := rfl
@[simp] theorem blk_sz (h : Matrix (Fin k) (Fin k) ℂ) (R : Fin k → ℂ) (a : Fin k) : blk h R a.succ 0 = 0 := rfl
@[simp] theorem blk_ss (h : Matrix (Fin k) (Fin k) ℂ) (R : Fin k → ℂ) (a b : Fin k) :
    blk h R a.succ b.succ = h a b := rfl

theorem blk_col (h : Matrix (Fin k) (Fin k) ℂ) (R : Fin k → ℂ) (a) : blk h R a 0 = if a = 0 then 1 else 0 := by
  refine Fin.cases ?_ (fun a => ?_) a <;> simp [Fin.succ_ne_zero]

theorem det_blk (h : Matrix (Fin k) (Fin k) ℂ) (R : Fin k → ℂ) : (blk h R).det = h.det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp only [blk_sz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, firstColumnBlockMatrix_apply_zero_zero, Fin.val_zero, pow_zero, one_mul,
    Fin.succAbove_zero]
  rfl

theorem blk_mul (β h : Matrix (Fin k) (Fin k) ℂ) (τ R : Fin k → ℂ) :
    blk β τ * blk h R = blk (β * h) (R + τ ᵥ* h) := by
  ext a b
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.vecMul, dotProduct]

theorem eq_blk (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hM : ∀ a, M a 0 = if a = 0 then 1 else 0) :
    M = blk (Matrix.of fun a b => M a.succ b.succ) (fun b => M 0 b.succ) := by
  ext a b
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
    simp [hM, Fin.succ_ne_zero]

theorem mul_inv_col (A M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hd : M.det ≠ 0)
    (hM : ∀ a, M a 0 = if a = 0 then 1 else 0) (a) : (A * M⁻¹) a 0 = A a 0 := by
  have h1 : A * M⁻¹ * M = A := Matrix.nonsing_inv_mul_cancel_right _ _ hd.isUnit
  conv_rhs => rw [← h1, Matrix.mul_apply]
  simp [hM]

def xc (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Fin (k + 1) → ℂ := fun a => g⁻¹ a 0

variable (s : (Fin (k + 1) → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ)

def mm (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  g * Matrix.of (s (xc g))

def hL (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun a b => mm s g a.succ b.succ

def TL (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Fin k → ℂ :=
  (fun b => mm s g 0 b.succ) ᵥ* (hL s g)⁻¹

variable {s} (hs : ∀ x, x ≠ 0 → (Matrix.of (s x)).det = 1 ∧ ∀ a, s x a 0 = x a)

theorem mulVec_xc (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hg : g.det ≠ 0) (a) :
    ∑ b, g a b * xc g b = if a = 0 then 1 else 0 := by
  have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hg.isUnit
  have := congrFun (congrFun h1 a) 0
  rwa [Matrix.mul_apply, Matrix.one_apply] at this

theorem xc_ne (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hg : g.det ≠ 0) : xc g ≠ 0 := by
  intro h
  have := mulVec_xc g hg 0
  simp [h] at this

include hs in
theorem mm_eq (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hg : g.det ≠ 0) :
    mm s g = blk (hL s g) (fun b => mm s g 0 b.succ) := by
  refine eq_blk _ fun a => ?_
  rw [← mulVec_xc g hg a, mm, Matrix.mul_apply]
  simp [(hs _ (xc_ne g hg)).2]

include hs in
theorem det_hL (g : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hg : g.det ≠ 0) : (hL s g).det = g.det := by
  have h1 : (mm s g).det = g.det := by rw [mm, Matrix.det_mul, (hs _ (xc_ne g hg)).1, mul_one]
  exact (det_blk _ _).symm.trans ((congrArg Matrix.det (mm_eq hs g hg)).symm.trans h1)

include hs in
theorem hL_mul (g γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hg : g.det ≠ 0) (hγ : γ.det ≠ 0)
    (hc : ∀ a, γ a 0 = if a = 0 then 1 else 0) (β : Matrix (Fin k) (Fin k) ℂ)
    (hβ : ∀ a b, β a b = γ a.succ b.succ) :
    hL s (γ * g) = β * hL s g ∧ TL s (γ * g) ᵥ* β = TL s g + fun b => γ 0 b.succ := by
  have hx : xc (γ * g) = xc g := by
    funext a
    simp only [xc]
    rw [Matrix.mul_inv_rev, mul_inv_col _ _ hγ hc]
  have hγ' : γ = blk β (fun b => γ 0 b.succ) := by
    have : β = Matrix.of fun a b => γ a.succ b.succ := by ext a b; simp [hβ]
    rw [this]; exact eq_blk γ hc
  have hβd : β.det ≠ 0 := fun h0 => hγ ((congrArg Matrix.det hγ').trans ((det_blk _ _).trans h0))
  have hhd : (hL s g).det ≠ 0 := (det_hL hs g hg).trans_ne hg
  have hm : mm s (γ * g) = blk (β * hL s g) ((fun b => mm s g 0 b.succ) + (fun b => γ 0 b.succ) ᵥ* hL s g) := by
    have e : mm s (γ * g) = γ * mm s g := by simp only [mm, hx, Matrix.mul_assoc]
    exact e.trans ((congrArg₂ (· * ·) hγ' (mm_eq hs g hg)).trans (blk_mul _ _ _ _))
  have h1 : hL s (γ * g) = β * hL s g := by
    ext a b; rw [hL, hm]; simp
  refine ⟨h1, ?_⟩
  have h2 : (fun b => mm s (γ * g) 0 b.succ) =
      (fun b => mm s g 0 b.succ) + (fun b => γ 0 b.succ) ᵥ* hL s g := by
    funext b; rw [hm, blk_zs]
  unfold TL
  rw [h1, h2]
  generalize hL s g = h at hhd ⊢
  generalize (fun b : Fin k => mm s g 0 b.succ) = R
  generalize (fun b : Fin k => γ 0 b.succ) = τ
  rw [Matrix.vecMul_vecMul, Matrix.mul_inv_rev, Matrix.nonsing_inv_mul_cancel_right _ _ hβd.isUnit,
    Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hhd.isUnit, Matrix.vecMul_one]

include hs in
theorem coord_inv (x : Fin (k + 1) → ℂ) (hx : x ≠ 0) (h : Matrix (Fin k) (Fin k) ℂ) (hh : h.det ≠ 0)
    (T : Fin k → ℂ) :
    xc (blk h (T ᵥ* h) * (Matrix.of (s x))⁻¹) = x ∧ hL s (blk h (T ᵥ* h) * (Matrix.of (s x))⁻¹) = h ∧
      TL s (blk h (T ᵥ* h) * (Matrix.of (s x))⁻¹) = T := by
  have hu : IsUnit (Matrix.of (s x)).det := by rw [(hs x hx).1]; exact isUnit_one
  have h1 : xc (blk h (T ᵥ* h) * (Matrix.of (s x))⁻¹) = x := by
    funext a
    simp only [xc]
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu,
      mul_inv_col _ _ (by rwa [det_blk]) (blk_col _ _)]
    exact (hs x hx).2 a
  have h2 : mm s (blk h (T ᵥ* h) * (Matrix.of (s x))⁻¹) = blk h (T ᵥ* h) := by
    rw [mm, h1, Matrix.nonsing_inv_mul_cancel_right _ _ hu]
  have h3 : hL s (blk h (T ᵥ* h) * (Matrix.of (s x))⁻¹) = h := by
    ext a b; rw [hL, h2]; simp
  refine ⟨h1, h3, ?_⟩
  rw [TL, h3, h2]
  simp only [blk_zs]
  show (T ᵥ* h) ᵥ* _ = _
  rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hh.isUnit, Matrix.vecMul_one]

section Meas
variable {X : Type} [MeasurableSpace X]

theorem meas_inv {j : ℕ} {A : X → Matrix (Fin j) (Fin j) ℂ} (hA : ∀ a b, Measurable fun p => A p a b) (a b) :
    Measurable fun p => (A p)⁻¹ a b := by
  have h0 : Measurable fun p => (fun a b => A p a b : Fin j → Fin j → ℂ) :=
    measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => hA a b
  have h1 : Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    Continuous.matrix_det (A := fun x : Fin j → Fin j → ℂ => Matrix.of x) continuous_id
  have h2 : Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).adjugate a b :=
    (Continuous.matrix_adjugate (A := fun x : Fin j → Fin j → ℂ => Matrix.of x) continuous_id).matrix_elem a b
  have h3 := (h1.measurable.inv.mul h2.measurable).comp h0
  have : (fun p => (A p)⁻¹ a b) = fun p => ((A p).det)⁻¹ * (A p).adjugate a b := by
    funext g; rw [Matrix.inv_def, Ring.inverse_eq_inv']; rfl
  rw [this]; exact h3

theorem meas_mul {j : ℕ} {A B : X → Matrix (Fin j) (Fin j) ℂ} (hA : ∀ a b, Measurable fun p => A p a b)
    (hB : ∀ a b, Measurable fun p => B p a b) (a b) : Measurable fun p => (A p * B p) a b := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun c _ => (hA a c).mul (hB c b)

theorem meas_vecMul {j : ℕ} {v : X → Fin j → ℂ} {B : X → Matrix (Fin j) (Fin j) ℂ}
    (hv : ∀ a, Measurable fun p => v p a)
    (hB : ∀ a b, Measurable fun p => B p a b) (b) : Measurable fun p => (v p ᵥ* B p) b := by
  simp only [Matrix.vecMul, dotProduct]
  exact Finset.measurable_sum _ fun c _ => (hv c).mul (hB c b)

theorem measurable_matrix_of_section_entries (hm : Measurable s) {v : X → Fin (k + 1) → ℂ} (hv : Measurable v) (a b) :
    Measurable fun p => Matrix.of (s (v p)) a b :=
  (measurable_pi_apply b).comp ((measurable_pi_apply a).comp (hm.comp hv))

theorem meas_mm (hm : Measurable s) {A : X → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hA : ∀ a b, Measurable fun p => A p a b) (a b) : Measurable fun p => mm s (A p) a b :=
  meas_mul hA (measurable_matrix_of_section_entries hm (measurable_pi_lambda _ fun a => meas_inv hA a 0)) a b

theorem meas_hL (hm : Measurable s) {A : X → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hA : ∀ a b, Measurable fun p => A p a b) (a b) : Measurable fun p => hL s (A p) a b :=
  meas_mm hm hA _ _

theorem meas_TL (hm : Measurable s) {A : X → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hA : ∀ a b, Measurable fun p => A p a b) (b) : Measurable fun p => TL s (A p) b :=
  meas_vecMul (fun _ => meas_mm hm hA _ _) (meas_inv (meas_hL hm hA)) b

theorem meas_blk {A : X → Matrix (Fin k) (Fin k) ℂ} {v : X → Fin k → ℂ}
    (hA : ∀ a b, Measurable fun p => A p a b) (hv : ∀ a, Measurable fun p => v p a) (a b) :
    Measurable fun p => blk (A p) (v p) a b := by
  refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;> simp [hA, hv]

theorem meas_det {j : ℕ} : Measurable fun x : Fin j → Fin j → ℂ => ‖(Matrix.of x).det‖ ^ 2 :=
  GlobalTheory.GLFirstColumn.continuous_detM.norm.measurable.pow_const 2

end Meas

theorem ae_ne_zero (ι : Type) [Fintype ι] (k : ℕ) : ∀ᵐ x : ι → Fin (k + 1) → ℂ, ∀ w, x w ≠ 0 := by
  haveI : SigmaFinite (volume : Measure (Fin (k + 1) → ℂ)) := inferInstance
  rw [ae_all_iff]
  intro w
  have h : ∀ᵐ y : Fin (k + 1) → ℂ, y ≠ 0 := by
    rw [ae_iff]; simp
  exact (Measure.quasiMeasurePreserving_eval (fun _ : ι => (volume : Measure (Fin (k + 1) → ℂ))) w).ae h

theorem coordinates : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ), 1 ≤ k → ∃ (hh : MatInf E (k + 1) → MatInf E k) (TT : MatInf E (k + 1) → VecInf E k), Measurable hh ∧ Measurable TT ∧ (∀ g, 0 < detNorm E (k + 1) g → detNorm E k (hh g) = detNorm E (k + 1) g) ∧ (∀ g γ : MatInf E (k + 1), 0 < detNorm E (k + 1) g → 0 < detNorm E (k + 1) γ → (∀ w a, γ w a 0 = if a = 0 then 1 else 0) → ∀ β : MatInf E k, (∀ w a b, β w a b = γ w a.succ b.succ) → hh (γ * g) = β * hh g ∧ ∀ w, TT (γ * g) w ᵥ* Matrix.of (β w) = TT g w + fun b => γ w 0 b.succ) ∧ ∀ (F : MatInf E k → ENNReal) (Q : VecInf E k → ENNReal) (Φ : VecInf E (k + 1) → ENNReal), Measurable F → Measurable Q → Measurable Φ → ∫⁻ g, F (hh g) * Q (TT g) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0) ∂(haarGL E (k + 1)) = (∫⁻ x, Φ x) * (∫⁻ T, Q T) * ∫⁻ h, F h * ENNReal.ofReal (detNorm E k h) ∂(haarGL E k) := by
  intro E _ _ k hk
  obtain ⟨s, hm, hs, hint⟩ := GlobalTheory.GLFirstColumn.haar_first_column k hk
  let hh : MatInf E (k + 1) → MatInf E k := fun g w a b => hL s (Matrix.of (g w)) a b
  let TT : MatInf E (k + 1) → VecInf E k := fun g w => TL s (Matrix.of (g w))
  have mh : Measurable hh :=
    measurable_pi_lambda (X := fun _ : InfinitePlace E => Fin k → Fin k → ℂ) _ fun w =>
      measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b =>
        meas_hL hm (A := fun g : MatInf E (k + 1) => Matrix.of (g w)) (measurable_entry w) a b
  have mT : Measurable TT :=
    measurable_pi_lambda _ fun w => measurable_pi_lambda _ fun b =>
        meas_TL hm (A := fun g : MatInf E (k + 1) => Matrix.of (g w)) (measurable_entry w) b
  refine ⟨hh, TT, mh, mT, fun g hg => ?_, fun g γ hg hγ hc β hβ => ?_, fun F Q Φ hF hQ hΦ => ?_⟩
  · rw [detNorm_pos_iff] at hg
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← det_hL hs _ (hg w)]; rfl
  · rw [detNorm_pos_iff] at hg hγ
    have := fun w => hL_mul hs _ _ (hg w) (hγ w) (hc w) (Matrix.of (β w)) (hβ w)
    exact ⟨matInf_ext fun w => (this w).1, fun w => (this w).2⟩
  have mx : Measurable fun g : MatInf E (k + 1) => (fun u a => (Matrix.of (g u))⁻¹ a 0 : VecInf E (k + 1)) :=
    measurable_pi_lambda _ fun w => measurable_pi_lambda _ fun a => measurable_inv_entry w a 0
  have mφ : Measurable fun g : MatInf E (k + 1) =>
      F (hh g) * Q (TT g) * Φ (fun u a => (Matrix.of (g u))⁻¹ a 0) :=
    ((hF.comp mh).mul (hQ.comp mT)).mul (hΦ.comp mx)
  have key := GlobalTheory.PiCoord.piCoord (InfinitePlace E) k
    (fun x h T a b => (blk (Matrix.of h) (T ᵥ* Matrix.of h) * (Matrix.of (s x))⁻¹) a b)
    (measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b =>
      meas_mul (meas_blk (fun a b => by simp only [Matrix.of_apply]; fun_prop)
        (meas_vecMul (fun a => by fun_prop) (fun a b => by simp only [Matrix.of_apply]; fun_prop)))
        (meas_inv (measurable_matrix_of_section_entries hm measurable_fst)) a b)
    (fun g => (‖(Matrix.of g).det‖ ^ 2)⁻¹ ^ (k + 1))
    (fun h => ‖(Matrix.of h).det‖ ^ 2 * (‖(Matrix.of h).det‖ ^ 2)⁻¹ ^ k)
    (meas_det.inv.pow_const _) (meas_det.mul (meas_det.inv.pow_const _))
    (fun g => by positivity) (fun g => by positivity) hint _ mφ
  have dens : ∀ (j : ℕ) (f : MatInf E j → ENNReal), Measurable f → ∫⁻ g, f g ∂(haarGL E j) =
      ∫⁻ g : InfinitePlace E → Fin j → Fin j → ℂ, f g * ENNReal.ofReal ((detNorm E j g)⁻¹ ^ j) := by
    intro j f hf
    have h1 : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
      (measurable_detNorm.inv.pow_const j).ennreal_ofReal
    refine (lintegral_withDensity_eq_lintegral_mul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))
      h1 hf).trans ?_
    exact lintegral_congr fun g => mul_comm _ _
  have mF : Measurable fun h : MatInf E k => F h * ENNReal.ofReal (detNorm E k h) :=
    hF.mul measurable_detNorm.ennreal_ofReal
  have mF' : Measurable fun h : InfinitePlace E → Fin k → Fin k → ℂ =>
      F h * ENNReal.ofReal (detNorm E k h) * ENNReal.ofReal ((detNorm E k h)⁻¹ ^ k) :=
    mF.mul (measurable_detNorm.inv.pow_const k).ennreal_ofReal
  rw [dens _ _ mφ, dens _ _ mF]
  have e1 : ∀ g : InfinitePlace E → Fin (k + 1) → Fin (k + 1) → ℂ, (detNorm E (k + 1) g)⁻¹ ^ (k + 1) =
      ∏ w, (‖(Matrix.of (g w)).det‖ ^ 2)⁻¹ ^ (k + 1) := by
    intro g; rw [Finset.prod_pow, Finset.prod_inv_distrib]; rfl
  simp only [e1]
  refine key.trans ?_
  rw [mul_assoc, ← lintegral_mul_const _ hΦ]
  refine lintegral_congr_ae ((ae_ne_zero (InfinitePlace E) k).mono fun x hx => ?_)
  simp only
  rw [← mul_assoc, ← lintegral_const_mul _ mF']
  refine lintegral_congr fun h => ?_
  have e2 : ∏ w, ‖(Matrix.of (h w)).det‖ ^ 2 * (‖(Matrix.of (h w)).det‖ ^ 2)⁻¹ ^ k =
      detNorm E k h * (detNorm E k h)⁻¹ ^ k := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow _ k, Finset.prod_inv_distrib]; rfl
  rw [e2, ENNReal.ofReal_mul (detNorm_nonneg (E := E) h)]
  rcases (detNorm_nonneg (E := E) (j := k) h).eq_or_lt with h0 | h0
  · simp [← h0]
  replace h0 := (detNorm_pos_iff (E := E) h).1 h0
  rw [← lintegral_const_mul _ hQ, ← lintegral_mul_const _ (hQ.const_mul _)]
  refine lintegral_congr fun T => ?_
  have := fun w => coord_inv hs (x w) (hx w) (Matrix.of (h w)) (h0 w) (T w)
  have a1 : hh (fun i a b => (blk (Matrix.of (h i)) (T i ᵥ* Matrix.of (h i)) * (Matrix.of (s (x i)))⁻¹) a b) = h :=
    matInf_ext fun w => (this w).2.1
  have a2 : TT (fun i a b => (blk (Matrix.of (h i)) (T i ᵥ* Matrix.of (h i)) * (Matrix.of (s (x i)))⁻¹) a b) = T :=
    funext fun w => (this w).2.2
  have a3 : (fun u a => (Matrix.of fun a b =>
      (blk (Matrix.of (h u)) (T u ᵥ* Matrix.of (h u)) * (Matrix.of (s (x u)))⁻¹) a b)⁻¹ a 0) = x :=
    funext fun w => (this w).1
  rw [a1, a2, a3]
  ring

end GlobalTheory.FirstColumnCoord
