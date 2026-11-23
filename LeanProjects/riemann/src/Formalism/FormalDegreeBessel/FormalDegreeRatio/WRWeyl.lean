import Formalism.FormalDegreeBessel.StatementWR

open scoped ContDiff Topology
open Filter

noncomputable section

namespace Formalism.QuantumDeterminants

namespace WirtingerDerivatives

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isOpen_omX (m : ℕ) : IsOpen (OmX m) := by
  have : OmX m = ⋂ l : Fin m, {x : Fin m → ℂ | x l ≠ 0} := by ext x; simp [OmX]
  rw [this]
  exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const

theorem top_add_one_le : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
  exact_mod_cast (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤)

theorem one_add_one_le : (1 : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω) := by
  have : ((1 : ℕ∞) : ℕ∞ω) + ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
    rw [← WithTop.coe_add]; exact WithTop.coe_le_coe.mpr le_top
  exact this

theorem two_le_smooth : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
  rw [minSmoothness_of_isRCLikeNormedField]
  have : (((2 : ℕ) : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top
  exact this

theorem top_ne_zero' : (∞ : ℕ∞ω) ≠ 0 := by
  exact WithTop.coe_ne_zero.mpr (by simp)

def Wc (u w : Fin m → ℂ) (s : ℂ) : ((Fin m → ℂ) →L[ℝ] E) →L[ℝ] E :=
  (ContinuousLinearMap.lsmul ℝ ℂ (1 / 2 : ℂ)).comp
    (ContinuousLinearMap.apply ℝ E u +
      (ContinuousLinearMap.lsmul ℝ ℂ s).comp (ContinuousLinearMap.apply ℝ E w))

theorem Wc_apply (u w : Fin m → ℂ) (s : ℂ) (T : (Fin m → ℂ) →L[ℝ] E) :
    Wc u w s T = (1 / 2 : ℂ) • (T u + s • T w) := by
  rfl

theorem wirt_eq (l : Fin m) (g : (Fin m → ℂ) → E) (x : Fin m → ℂ) :
    wirt l g x = Wc (Pi.single l 1) (Pi.single l Complex.I) (-Complex.I) (fderiv ℝ g x) := by
  rw [Wc_apply, wirt, neg_smul, sub_eq_add_neg]

theorem wirtBar_eq (l : Fin m) (g : (Fin m → ℂ) → E) (x : Fin m → ℂ) :
    wirtBar l g x = Wc (Pi.single l 1) (Pi.single l Complex.I) Complex.I (fderiv ℝ g x) := by
  rw [Wc_apply, wirtBar]

theorem hasFDerivAt_star_apply (k : Fin m) (x : Fin m → ℂ) :
    HasFDerivAt (fun y : Fin m → ℂ => star (y k))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (ContinuousLinearMap.proj k)) x := by
  exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℂ) k)).hasFDerivAt

theorem hasFDerivAt_inv_apply (k : Fin m) {x : Fin m → ℂ} (hx : x k ≠ 0) :
    HasFDerivAt (fun y : Fin m → ℂ => (y k)⁻¹)
      (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(x k ^ 2)⁻¹)).restrictScalars ℝ).comp
        (ContinuousLinearMap.proj k)) x := by
  exact ((hasDerivAt_inv hx).hasFDerivAt.restrictScalars ℝ).comp x
    (hasFDerivAt_apply (𝕜 := ℝ) k x)

def Reg (g : (Fin m → ℂ) → E) : Prop := ∀ x ∈ OmX m, ContDiffAt ℝ ∞ g x

theorem reg_of_mem {f : (Fin m → ℂ) → E} (hf : f ∈ WSm m E) : Reg f := by
  intro x hx
  exact hf.1.contDiffAt ((isOpen_omX m).mem_nhds hx)

theorem diff_of_reg {g : (Fin m → ℂ) → E} {x : Fin m → ℂ} (hg : ContDiffAt ℝ ∞ g x) :
    DifferentiableAt ℝ g x := by
  exact hg.differentiableAt top_ne_zero'

theorem diff_fderiv {g : (Fin m → ℂ) → E} {x : Fin m → ℂ} (hg : ContDiffAt ℝ ∞ g x) :
    DifferentiableAt ℝ (fderiv ℝ g) x := by
  exact (hg.fderiv_right (m := 1) one_add_one_le).differentiableAt one_ne_zero

theorem contDiffAt_Wc {g : (Fin m → ℂ) → E} {x : Fin m → ℂ} (hg : ContDiffAt ℝ ∞ g x)
    (u w : Fin m → ℂ) (s : ℂ) : ContDiffAt ℝ ∞ (fun y => Wc u w s (fderiv ℝ g y)) x := by
  exact (Wc u w s).contDiff.contDiffAt.comp x (hg.fderiv_right (m := ∞) top_add_one_le)

theorem fderiv_Wc {g : (Fin m → ℂ) → E} {x : Fin m → ℂ} (hg : ContDiffAt ℝ ∞ g x)
    (u w : Fin m → ℂ) (s : ℂ) :
    fderiv ℝ (fun y => Wc u w s (fderiv ℝ g y)) x = (Wc u w s).comp (fderiv ℝ (fderiv ℝ g) x) := by
  exact ((Wc u w s).hasFDerivAt.comp x (diff_fderiv hg).hasFDerivAt).fderiv

theorem Wc_comm {g : (Fin m → ℂ) → E} {x : Fin m → ℂ} (hg : ContDiffAt ℝ ∞ g x)
    (u w : Fin m → ℂ) (s : ℂ) (u' w' : Fin m → ℂ) (s' : ℂ) :
    Wc u w s (fderiv ℝ (fun y => Wc u' w' s' (fderiv ℝ g y)) x) =
      Wc u' w' s' (fderiv ℝ (fun y => Wc u w s (fderiv ℝ g y)) x) := by
  have hs := hg.isSymmSndFDerivAt two_le_smooth
  rw [fderiv_Wc hg, fderiv_Wc hg]
  simp only [Wc_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, map_add, map_smul]
  rw [hs u' u, hs u' w, hs w' u, hs w' w]
  module

theorem fderiv_smul_apply {a : (Fin m → ℂ) → ℂ} {h : (Fin m → ℂ) → E} {x : Fin m → ℂ}
    (ha : DifferentiableAt ℝ a x) (hh : DifferentiableAt ℝ h x) (v : Fin m → ℂ) :
    fderiv ℝ (fun y => a y • h y) x v = a x • fderiv ℝ h x v + fderiv ℝ a x v • h x := by
  have H : HasFDerivAt (fun y => a y • h y)
      (a x • fderiv ℝ h x + (fderiv ℝ a x).smulRight (h x)) x :=
    ha.hasFDerivAt.smul hh.hasFDerivAt
  rw [H.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply]

theorem Wc_smul {a : (Fin m → ℂ) → ℂ} {h : (Fin m → ℂ) → E} {x : Fin m → ℂ}
    (ha : DifferentiableAt ℝ a x) (hh : DifferentiableAt ℝ h x) (u w : Fin m → ℂ) (s : ℂ) :
    Wc u w s (fderiv ℝ (fun y => a y • h y) x) =
      Wc u w s (fderiv ℝ a x) • h x + a x • Wc u w s (fderiv ℝ h x) := by
  rw [Wc_apply, Wc_apply, Wc_apply, fderiv_smul_apply ha hh, fderiv_smul_apply ha hh]
  simp only [smul_eq_mul]
  module

theorem wirt_fun (l : Fin m) (g : (Fin m → ℂ) → E) :
    wirt l g = fun y => Wc (Pi.single l 1) (Pi.single l Complex.I) (-Complex.I) (fderiv ℝ g y) := by
  funext y
  exact wirt_eq l g y

theorem wirtBar_fun (l : Fin m) (g : (Fin m → ℂ) → E) :
    wirtBar l g = fun y => Wc (Pi.single l 1) (Pi.single l Complex.I) Complex.I (fderiv ℝ g y) := by
  funext y
  exact wirtBar_eq l g y

theorem Wc_hol (k l : Fin m) (c : ℂ) (T : (Fin m → ℂ) →L[ℝ] ℂ) (hT : ∀ v, T v = c * v k) :
    Wc (Pi.single l 1) (Pi.single l Complex.I) (-Complex.I) T = (if l = k then c else 0) ∧
      Wc (Pi.single l 1) (Pi.single l Complex.I) Complex.I T = 0 := by
  refine ⟨?_, ?_⟩ <;> rw [Wc_apply, hT, hT] <;> by_cases hl : l = k
  · simp only [hl, Pi.single_eq_same, if_true, smul_eq_mul]
    linear_combination (-c / 2) * Complex.I_sq
  · simp [hl, Pi.single_eq_of_ne (Ne.symm hl)]
  · simp only [hl, Pi.single_eq_same, smul_eq_mul]
    linear_combination (c / 2) * Complex.I_sq
  · simp [Pi.single_eq_of_ne (Ne.symm hl)]

theorem Wc_anti (k l : Fin m) (c : ℂ) (T : (Fin m → ℂ) →L[ℝ] ℂ) (hT : ∀ v, T v = c * star (v k)) :
    Wc (Pi.single l 1) (Pi.single l Complex.I) (-Complex.I) T = 0 ∧
      Wc (Pi.single l 1) (Pi.single l Complex.I) Complex.I T = (if l = k then c else 0) := by
  refine ⟨?_, ?_⟩ <;> rw [Wc_apply, hT, hT] <;> by_cases hl : l = k
  · simp only [hl, Pi.single_eq_same, smul_eq_mul, star_one, Complex.star_def, Complex.conj_I]
    linear_combination (c / 2) * Complex.I_sq
  · simp [Pi.single_eq_of_ne (Ne.symm hl)]
  · simp only [hl, Pi.single_eq_same, if_true, smul_eq_mul, star_one, Complex.star_def,
      Complex.conj_I]
    linear_combination (-c / 2) * Complex.I_sq
  · simp [hl, Pi.single_eq_of_ne (Ne.symm hl)]

def coef (k : Fin m) : Fin 6 → (Fin m → ℂ) → ℂ
  | 0 => fun y => y k
  | 1 => fun y => y k
  | 2 => fun y => (y k)⁻¹
  | 3 => fun y => star (y k)
  | 4 => fun y => star (y k)
  | 5 => fun y => (star (y k))⁻¹

def ck (k : Fin m) : Fin 6 → (Fin m → ℂ) → ℂ
  | 0 => fun _ => 1
  | 1 => fun _ => 1
  | 2 => fun y => -((y k) ^ 2)⁻¹
  | 3 => fun _ => 1
  | 4 => fun _ => 1
  | 5 => fun y => -((star (y k)) ^ 2)⁻¹

def Dop (k : Fin m) : Fin 6 → ((Fin m → ℂ) → E) → (Fin m → ℂ) → E
  | 0 => wirt k
  | 1 => fun g => g
  | 2 => fun g => g
  | 3 => wirtBar k
  | 4 => fun g => g
  | 5 => fun g => g

theorem star_fun_eq (k : Fin m) :
    (fun y : Fin m → ℂ => star (y k)) = fun y => (Complex.conjCLE : ℂ →L[ℝ] ℂ) (y k) := by
  rfl

theorem fderiv_coef {k : Fin m} {x : Fin m → ℂ} (hx : x ∈ OmX m) (j : Fin 6) (v : Fin m → ℂ) :
    fderiv ℝ (coef k j) x v =
      if (j : ℕ) < 3 then ck k j x * v k else ck k j x * star (v k) := by
  have hxk : x k ≠ 0 := hx k
  match j with
  | 0 =>
    show fderiv ℝ (fun y : Fin m → ℂ => y k) x v = _
    rw [(hasFDerivAt_apply (𝕜 := ℝ) k x).fderiv]
    simp [ck]
  | 1 =>
    show fderiv ℝ (fun y : Fin m → ℂ => y k) x v = _
    rw [(hasFDerivAt_apply (𝕜 := ℝ) k x).fderiv]
    simp [ck]
  | 2 =>
    show fderiv ℝ (fun y : Fin m → ℂ => (y k)⁻¹) x v = _
    rw [(hasFDerivAt_inv_apply k hxk).fderiv]
    simp [ck, mul_comm]
  | 3 =>
    show fderiv ℝ (fun y : Fin m → ℂ => star (y k)) x v = _
    rw [(hasFDerivAt_star_apply k x).fderiv]
    simp [ck]
  | 4 =>
    show fderiv ℝ (fun y : Fin m → ℂ => star (y k)) x v = _
    rw [(hasFDerivAt_star_apply k x).fderiv]
    simp [ck]
  | 5 =>
    show fderiv ℝ (fun y : Fin m → ℂ => (star (y k))⁻¹) x v = _
    have hs : star (x k) ≠ 0 := star_ne_zero.mpr hxk
    have h5 : HasFDerivAt (fun y : Fin m → ℂ => (star (y k))⁻¹)
        (((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(star (x k) ^ 2)⁻¹)).restrictScalars ℝ).comp
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℂ) k))) x :=
      ((hasDerivAt_inv hs).hasFDerivAt.restrictScalars ℝ).comp x (hasFDerivAt_star_apply k x)
    rw [h5.fderiv]
    simp [ck, mul_comm]

theorem wirt_coef {k : Fin m} {x : Fin m → ℂ} (hx : x ∈ OmX m) (l : Fin m) (j : Fin 6) :
    wirt l (coef k j) x = if (j : ℕ) < 3 ∧ l = k then ck k j x else 0 := by
  rw [wirt, fderiv_coef hx, fderiv_coef hx]
  by_cases hj : (j : ℕ) < 3 <;> by_cases hl : l = k
  · simp only [hl, hj, if_true, and_self, Pi.single_eq_same, smul_eq_mul]
    linear_combination (-(ck k j x) / 2) * Complex.I_sq
  · simp [hj, hl, Pi.single_eq_of_ne (Ne.symm hl)]
  · simp only [hl, hj, if_false, false_and, Pi.single_eq_same, smul_eq_mul, star_one,
      Complex.star_def, Complex.conj_I]
    linear_combination (ck k j x / 2) * Complex.I_sq
  · simp [hj, hl, Pi.single_eq_of_ne (Ne.symm hl)]

theorem wirtBar_coef {k : Fin m} {x : Fin m → ℂ} (hx : x ∈ OmX m) (l : Fin m) (j : Fin 6) :
    wirtBar l (coef k j) x = if ¬ (j : ℕ) < 3 ∧ l = k then ck k j x else 0 := by
  rw [wirtBar, fderiv_coef hx, fderiv_coef hx]
  by_cases hj : (j : ℕ) < 3 <;> by_cases hl : l = k
  · simp only [hl, hj, if_true, not_true_eq_false, false_and, if_false, Pi.single_eq_same,
      smul_eq_mul]
    linear_combination (ck k j x / 2) * Complex.I_sq
  · simp [hj, hl, Pi.single_eq_of_ne (Ne.symm hl)]
  · simp only [hl, hj, if_false, not_false_eq_true, and_self, if_true, Pi.single_eq_same,
      smul_eq_mul, star_one, Complex.star_def, Complex.conj_I]
    linear_combination (-(ck k j x) / 2) * Complex.I_sq
  · simp [hj, hl, Pi.single_eq_of_ne (Ne.symm hl)]

theorem contDiffAt_star_apply (k : Fin m) (x : Fin m → ℂ) :
    ContDiffAt ℝ ∞ (fun y : Fin m → ℂ => star (y k)) x := by
  rw [star_fun_eq]
  exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp (contDiff_apply ℝ ℂ k)).contDiffAt

theorem coef_contDiffAt {k : Fin m} {x : Fin m → ℂ} (hx : x ∈ OmX m) (j : Fin 6) :
    ContDiffAt ℝ ∞ (coef k j) x := by
  have hxk : x k ≠ 0 := hx k
  match j with
  | 0 => exact (contDiff_apply ℝ ℂ k).contDiffAt
  | 1 => exact (contDiff_apply ℝ ℂ k).contDiffAt
  | 2 => exact (contDiffAt_inv ℝ hxk).comp x (contDiff_apply ℝ ℂ k).contDiffAt
  | 3 => exact contDiffAt_star_apply k x
  | 4 => exact contDiffAt_star_apply k x
  | 5 => exact (contDiffAt_inv ℝ (star_ne_zero.mpr hxk)).comp x (contDiffAt_star_apply k x)

theorem opL_ev (k : Fin m) (j : Fin 6) (g : (Fin m → ℂ) → E) {x : Fin m → ℂ} (hx : x ∈ OmX m) :
    opL k j g =ᶠ[𝓝 x] fun y => coef k j y • Dop k j g y := by
  have hev : ∀ᶠ y in 𝓝 x, y ∈ OmX m := (isOpen_omX m).mem_nhds hx
  match j with
  | 0 =>
    filter_upwards [hev] with y hy
    show pOp k g y = y k • wirt k g y
    simp [pOp, hy]
  | 1 => exact Filter.Eventually.of_forall fun y => rfl
  | 2 => exact Filter.Eventually.of_forall fun y => rfl
  | 3 =>
    filter_upwards [hev] with y hy
    show pbOp k g y = star (y k) • wirtBar k g y
    simp [pbOp, hy]
  | 4 => exact Filter.Eventually.of_forall fun y => rfl
  | 5 => exact Filter.Eventually.of_forall fun y => rfl

theorem opL_on (k : Fin m) (j : Fin 6) (g : (Fin m → ℂ) → E) {x : Fin m → ℂ} (hx : x ∈ OmX m) :
    opL k j g x = coef k j x • Dop k j g x := by
  exact (opL_ev k j g hx).self_of_nhds

theorem opL_off (k : Fin m) (j : Fin 6) (g : (Fin m → ℂ) → E) {x : Fin m → ℂ} (hx : x ∉ OmX m)
    (h0 : g x = 0) : opL k j g x = 0 := by
  match j with
  | 0 => show pOp k g x = 0; simp [pOp, hx]
  | 1 => show x k • g x = 0; rw [h0, smul_zero]
  | 2 => show (x k)⁻¹ • g x = 0; rw [h0, smul_zero]
  | 3 => show pbOp k g x = 0; simp [pbOp, hx]
  | 4 => show star (x k) • g x = 0; rw [h0, smul_zero]
  | 5 => show (star (x k))⁻¹ • g x = 0; rw [h0, smul_zero]

theorem reg_Dop {g : (Fin m → ℂ) → E} (hg : Reg g) (k : Fin m) (j : Fin 6) : Reg (Dop k j g) := by
  intro x hx
  match j with
  | 0 =>
    show ContDiffAt ℝ ∞ (wirt k g) x
    rw [wirt_fun]
    exact contDiffAt_Wc (hg x hx) _ _ _
  | 1 => exact hg x hx
  | 2 => exact hg x hx
  | 3 =>
    show ContDiffAt ℝ ∞ (wirtBar k g) x
    rw [wirtBar_fun]
    exact contDiffAt_Wc (hg x hx) _ _ _
  | 4 => exact hg x hx
  | 5 => exact hg x hx

theorem reg_opL {g : (Fin m → ℂ) → E} (hg : Reg g) (k : Fin m) (j : Fin 6) : Reg (opL k j g) := by
  intro x hx
  exact ((coef_contDiffAt hx j).smul (reg_Dop hg k j x hx)).congr_of_eventuallyEq (opL_ev k j g hx)

def dco (l : Fin m) (i : Fin 6) (k : Fin m) (j : Fin 6) (x : Fin m → ℂ) : ℂ :=
  match i with
  | 0 => wirt l (coef k j) x
  | 3 => wirtBar l (coef k j) x
  | _ => 0

theorem Dop_opL {g : (Fin m → ℂ) → E} (hg : Reg g) {x : Fin m → ℂ} (hx : x ∈ OmX m)
    (l k : Fin m) (i j : Fin 6) :
    Dop l i (opL k j g) x = dco l i k j x • Dop k j g x + coef k j x • Dop l i (Dop k j g) x := by
  have hc := diff_of_reg (coef_contDiffAt (k := k) hx j)
  have hd := diff_of_reg (reg_Dop hg k j x hx)
  have hfe : fderiv ℝ (opL k j g) x = fderiv ℝ (fun y => coef k j y • Dop k j g y) x :=
    (opL_ev k j g hx).fderiv_eq
  match i with
  | 0 =>
    show wirt l (opL k j g) x = wirt l (coef k j) x • Dop k j g x + coef k j x • wirt l (Dop k j g) x
    rw [wirt_eq, wirt_eq, wirt_eq, hfe, Wc_smul hc hd]
  | 1 =>
    show opL k j g x = (0 : ℂ) • Dop k j g x + coef k j x • Dop k j g x
    rw [opL_on k j g hx, zero_smul, zero_add]
  | 2 =>
    show opL k j g x = (0 : ℂ) • Dop k j g x + coef k j x • Dop k j g x
    rw [opL_on k j g hx, zero_smul, zero_add]
  | 3 =>
    show wirtBar l (opL k j g) x =
      wirtBar l (coef k j) x • Dop k j g x + coef k j x • wirtBar l (Dop k j g) x
    rw [wirtBar_eq, wirtBar_eq, wirtBar_eq, hfe, Wc_smul hc hd]
  | 4 =>
    show opL k j g x = (0 : ℂ) • Dop k j g x + coef k j x • Dop k j g x
    rw [opL_on k j g hx, zero_smul, zero_add]
  | 5 =>
    show opL k j g x = (0 : ℂ) • Dop k j g x + coef k j x • Dop k j g x
    rw [opL_on k j g hx, zero_smul, zero_add]

theorem Dop_comm {g : (Fin m → ℂ) → E} (hg : Reg g) {x : Fin m → ℂ} (hx : x ∈ OmX m)
    (l k : Fin m) (i j : Fin 6) : Dop l i (Dop k j g) x = Dop k j (Dop l i g) x := by
  match i with
  | 0 =>
    match j with
    | 0 =>
      show wirt l (wirt k g) x = wirt k (wirt l g) x
      rw [wirt_fun k g, wirt_fun l g, wirt_eq l, wirt_eq k]
      exact Wc_comm (hg x hx) _ _ _ _ _ _
    | 3 =>
      show wirt l (wirtBar k g) x = wirtBar k (wirt l g) x
      rw [wirtBar_fun k g, wirt_fun l g, wirt_eq l, wirtBar_eq k]
      exact Wc_comm (hg x hx) _ _ _ _ _ _
    | 1 => rfl
    | 2 => rfl
    | 4 => rfl
    | 5 => rfl
  | 3 =>
    match j with
    | 0 =>
      show wirtBar l (wirt k g) x = wirt k (wirtBar l g) x
      rw [wirt_fun k g, wirtBar_fun l g, wirtBar_eq l, wirt_eq k]
      exact Wc_comm (hg x hx) _ _ _ _ _ _
    | 3 =>
      show wirtBar l (wirtBar k g) x = wirtBar k (wirtBar l g) x
      rw [wirtBar_fun k g, wirtBar_fun l g, wirtBar_eq l, wirtBar_eq k]
      exact Wc_comm (hg x hx) _ _ _ _ _ _
    | 1 => rfl
    | 2 => rfl
    | 4 => rfl
    | 5 => rfl
  | 1 => rfl
  | 2 => rfl
  | 4 => rfl
  | 5 => rfl

theorem dco_zero {x : Fin m → ℂ} (hx : x ∈ OmX m) (l k : Fin m) (i j : Fin 6)
    (hc : l ≠ k ∨ (holoIdx i ↔ ¬ holoIdx j)) : dco l i k j x = 0 := by
  match i with
  | 0 =>
    show wirt l (coef k j) x = 0
    rw [wirt_coef hx, if_neg]
    rintro ⟨hj, hlk⟩
    rcases hc with h | h
    · exact h hlk
    · exact (h.mp (show holoIdx (0 : Fin 6) by unfold holoIdx; decide)) hj
  | 3 =>
    show wirtBar l (coef k j) x = 0
    rw [wirtBar_coef hx, if_neg]
    rintro ⟨hj, hlk⟩
    rcases hc with h | h
    · exact h hlk
    · exact absurd (h.mpr hj) (show ¬ holoIdx (3 : Fin 6) by unfold holoIdx; decide)
  | 1 => rfl
  | 2 => rfl
  | 4 => rfl
  | 5 => rfl

end WirtingerDerivatives

open WirtingerDerivatives

theorem commuting_functional_holds : CommFun := by
  intro m E _ _ l k i j f hf hc
  have hr := reg_of_mem hf
  have hc' : k ≠ l ∨ (holoIdx j ↔ ¬ holoIdx i) := by
    rcases hc with h | h
    · exact Or.inl (Ne.symm h)
    · right
      constructor
      · intro hj hi
        exact (h.mp hi) hj
      · intro hi
        by_contra hj
        exact hi (h.mpr hj)
  funext x
  by_cases hx : x ∈ OmX m
  · rw [opL_on l i _ hx, opL_on k j _ hx, Dop_opL hr hx, Dop_opL hr hx, dco_zero hx l k i j hc,
      dco_zero hx k l j i hc', zero_smul, zero_add, zero_smul, zero_add, Dop_comm hr hx,
      smul_smul, smul_smul, mul_comm]
  · rw [opL_off l i _ hx (opL_off k j f hx (hf.2 x hx)),
      opL_off k j _ hx (opL_off l i f hx (hf.2 x hx))]

theorem weyl_functional_holds : WeylFun := by
  intro m E _ _ l f hf
  have hr := reg_of_mem hf
  have h0 : ∀ x, x ∉ OmX m → f x = 0 := hf.2
  have hnot : ∀ x : Fin m → ℂ, x l = 0 → x ∉ OmX m := fun x h hx => hx l h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext x
    simp only [cOp, ciOp, smul_smul]
    by_cases h : x l = 0
    · rw [h0 x (hnot x h), smul_zero]
    · rw [mul_inv_cancel₀ h, one_smul]
  · funext x
    simp only [cOp, ciOp, smul_smul]
    by_cases h : x l = 0
    · rw [h0 x (hnot x h), smul_zero]
    · rw [inv_mul_cancel₀ h, one_smul]
  · funext x
    by_cases hx : x ∈ OmX m
    · have e := Dop_opL hr hx l l 0 1
      have hw : wirt l (coef l 1) x = 1 := by
        rw [wirt_coef hx, if_pos ⟨by decide, rfl⟩]
        rfl
      change opL l 0 (opL l 1 f) x = _
      rw [opL_on l 0 _ hx]
      change x l • Dop l 0 (opL l 1 f) x = _
      rw [e]
      change x l • (wirt l (coef l 1) x • f x + x l • wirt l f x) = x l • pOp l f x + x l • f x
      simp only [pOp, hx, if_true, hw, one_smul]
      rw [smul_add, add_comm]
    · simp only [Pi.add_apply, pOp, cOp, hx, if_false, h0 x hx, smul_zero, add_zero]
  · funext x
    simp only [cbOp, cbiOp, smul_smul]
    by_cases h : x l = 0
    · rw [h0 x (hnot x h), smul_zero]
    · rw [mul_inv_cancel₀ (star_ne_zero.mpr h), one_smul]
  · funext x
    simp only [cbOp, cbiOp, smul_smul]
    by_cases h : x l = 0
    · rw [h0 x (hnot x h), smul_zero]
    · rw [inv_mul_cancel₀ (star_ne_zero.mpr h), one_smul]
  · funext x
    by_cases hx : x ∈ OmX m
    · have e := Dop_opL hr hx l l 3 4
      have hw : wirtBar l (coef l 4) x = 1 := by
        rw [wirtBar_coef hx, if_pos ⟨by decide, rfl⟩]
        rfl
      change opL l 3 (opL l 4 f) x = _
      rw [opL_on l 3 _ hx]
      change star (x l) • Dop l 3 (opL l 4 f) x = _
      rw [e]
      change star (x l) • (wirtBar l (coef l 4) x • f x + star (x l) • wirtBar l f x) =
        star (x l) • pbOp l f x + star (x l) • f x
      simp only [pbOp, hx, if_true, hw, one_smul]
      rw [smul_add, add_comm]
    · simp only [Pi.add_apply, pbOp, cbOp, hx, if_false, h0 x hx, smul_zero, add_zero]

end Formalism.QuantumDeterminants
