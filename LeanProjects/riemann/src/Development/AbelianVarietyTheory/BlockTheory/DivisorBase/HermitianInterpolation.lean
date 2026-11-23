import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

open Matrix Filter Topology Set GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation

structure IsCutoff (χ : ℝ → ℝ) : Prop where

  smooth : ContDiffOn ℝ ∞ χ (Ici 0)

  mem : ∀ y, 0 ≤ y → χ y ∈ Icc (0 : ℝ) 1

  eq_one : ∀ y ∈ Icc (0 : ℝ) 2, χ y = 1

  eq_zero : ∀ y, 3 ≤ y → χ y = 0

  smooth_sqrt : ContDiffOn ℝ ∞ (fun y => √(χ y)) (Ici 0)

variable {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n]

def cutWeight (χ : ℝ → ℝ) (κ R : ℝ) (r : (ι → ℂ) → ℝ) (z : ι → ℂ) : ℝ :=
  χ (Real.log (r z) / Real.log R) / (1 + (r z / R) ^ κ)

def interp (H₀ H : (ι → ℂ) → Matrix n n ℂ) (s : (ι → ℂ) → ℝ) (z : ι → ℂ) : Matrix n n ℂ :=
  ((1 - s z : ℝ) : ℂ) • H₀ z + ((s z : ℝ) : ℂ) • H z

def IsWeight (χ : ℝ → ℝ) (κ : ℝ) (r s : (ι → ℂ) → ℝ) : Prop :=
  (∃ c ∈ Icc (0 : ℝ) 1, s = fun _ => c) ∨
    ∃ t ∈ Icc (0 : ℝ) 1, ∃ R : ℝ, 2 ≤ R ∧ s = fun z => t * cutWeight χ κ R r z

def PowComparable (U : Set (ι → ℂ)) (r : (ι → ℂ) → ℝ) (C : ℝ)
    (H₀ H : (ι → ℂ) → Matrix n n ℂ) : Prop :=
  ∀ z ∈ U, ∀ v : n → ℂ,
    r z ^ (-C) * (form (H₀ z) v v).re ≤ (form (H z) v v).re ∧
      (form (H z) v v).re ≤ r z ^ C * (form (H₀ z) v v).re

def gradForm (r : (ι → ℂ) → ℝ) (z ξ η : ι → ℂ) : ℂ :=
  kappa * (del (fun x => (r x : ℂ)) z ξ * dbar (fun x => (r x : ℂ)) z η)

def IsBlockDiag {σ : Type} (blk : n → σ) (U : Set (ι → ℂ)) (H : (ι → ℂ) → Matrix n n ℂ) : Prop :=
  ∀ z ∈ U, ∀ a b, blk a ≠ blk b → H z a b = 0

structure IsData (Cμ C₀ C₂ C₃ CP : ℝ) (U : Set (ι → ℂ)) (H₀ H : (ι → ℂ) → Matrix n n ℂ)
    (r : (ι → ℂ) → ℝ) (G : (ι → ℂ) → Matrix ι ι ℂ) : Prop where

  pos₀ : IsPosFrame U H₀

  pos : IsPosFrame U H

  smooth_r : ContDiffOn ℝ ∞ r U

  exp_le : ∀ z ∈ U, Real.exp 1 ≤ r z

  smooth_G : ∀ k l, ContDiffOn ℝ ∞ (fun x => G x k l) U

  posSemidef_G : ∀ z ∈ U, (G z).PosSemidef

  comparable : PowComparable U r Cμ H₀ H

  conn_le : OneFormBound U H₀ G (fun z ξ => conn H z ξ - conn H₀ z ξ) C₂

  curv_le : TwoFormBound U H G (curv H) C₃

  curv₀_le : TwoFormBound U H₀ G (curv H₀) C₀

  grad_le : ∀ z ∈ U, FormLe (fun ξ η => gradForm r z ξ η / ((r z : ℂ) ^ 2))
    fun ξ η => CP * formOf (G z) ξ η

  ddc_log_le : ∀ z ∈ U, FormAbsLe (ddc (fun x => Real.log (r x)) z) CP (formOf (G z))

def Conclusion (Cμ κ : ℝ) (χ : ℝ → ℝ) (C : ℝ) (U : Set (ι → ℂ)) (H₀ H : (ι → ℂ) → Matrix n n ℂ)
    (r : (ι → ℂ) → ℝ) (G : (ι → ℂ) → Matrix ι ι ℂ) : Prop :=

  (∀ s, IsWeight χ κ r s →
    IsPosFrame U (interp H₀ H s) ∧
    TwoFormBound U (interp H₀ H s) G (curv (interp H₀ H s)) C ∧
    PowComparable U r Cμ H₀ (interp H₀ H s) ∧
    ∀ (σ : Type) (blk : n → σ), IsBlockDiag blk U H₀ → IsBlockDiag blk U H →
      IsBlockDiag blk U (interp H₀ H s)) ∧

  (∀ t ∈ Icc (0 : ℝ) 1, ∀ R : ℝ, 2 ≤ R →
    (∀ z ∈ U, R ^ 3 ≤ r z → interp H₀ H (fun x => t * cutWeight χ κ R r x) z = H₀ z) ∧
    ∀ V : Set (ι → ℂ), U ⊆ V → IsPosFrame V H₀ →
      (∀ z ∈ V \ U, Tendsto r (𝓝[U] z) atTop) →
      IsPosFrame V fun z => open Classical in
        if z ∈ U then interp H₀ H (fun x => t * cutWeight χ κ R r x) z else H₀ z) ∧

  ∀ K : Set (ι → ℂ), IsCompact K → K ⊆ U → ∀ (k : ℕ) (a b : n),
    TendstoUniformlyOn
      (fun (R : ℝ) z => iteratedFDeriv ℝ k (fun x => interp H₀ H (cutWeight χ κ R r) x a b) z)
      (iteratedFDeriv ℝ k fun x => H x a b) atTop K

def InterpCurvBound : Prop :=
  ∀ (Cμ C₀ C₂ C₃ CP κ : ℝ) (χ : ℝ → ℝ), 2 * Cμ + 2 < κ → IsCutoff χ →
    ∃ C : ℝ, ∀ (ι n : Type) [Fintype ι] [Fintype n] [DecidableEq n] (U : Set (ι → ℂ))
      (H₀ H : (ι → ℂ) → Matrix n n ℂ) (r : (ι → ℂ) → ℝ) (G : (ι → ℂ) → Matrix ι ι ℂ),
      IsData Cμ C₀ C₂ C₃ CP U H₀ H r G → Conclusion Cμ κ χ C U H₀ H r G

theorem isCutoff_sq : IsCutoff fun y => Real.smoothTransition (3 - y) ^ 2 := by
  have h : ContDiff ℝ ∞ fun y : ℝ => Real.smoothTransition (3 - y) :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)
  refine ⟨(h.pow 2).contDiffOn, fun y _ => ⟨sq_nonneg _, ?_⟩, fun y hy => ?_, fun y hy => ?_, ?_⟩
  · exact pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
  · rw [Real.smoothTransition.one_of_one_le (by linarith [hy.2]), one_pow]
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; norm_num
  · simp only [Real.sqrt_sq (Real.smoothTransition.nonneg _)]
    exact h.contDiffOn

theorem isData_halfPlane :
    IsData (ι := Unit) (n := Unit) 1 0 1 0 1 {z | 0 < (z ()).re} (fun _ => 1)
      (fun z => ((Real.exp (1 + (z ()).re) : ℝ) : ℂ) • 1) (fun z => Real.exp (1 + (z ()).re))
      fun _ => 1 := by
  let L : (Unit → ℂ) →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.proj ())
  have hu : ContDiff ℝ ∞ fun z : Unit → ℂ => 1 + (z ()).re := contDiff_const.add L.contDiff
  have hr : ContDiff ℝ ∞ fun z : Unit → ℂ => Real.exp (1 + (z ()).re) := hu.exp
  have ho : IsOpen {z : Unit → ℂ | 0 < (z ()).re} := isOpen_lt continuous_const L.continuous
  have h1 : (1 : Matrix Unit Unit ℂ).PosDef := PosDef.one
  have hp : ∀ z : Unit → ℂ,
      (((Real.exp (1 + (z ()).re) : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ)).PosDef := fun z =>
    h1.smul (by exact_mod_cast Real.exp_pos _)
  have hd : ∀ z ξ : Unit → ℂ, del (fun x : Unit → ℂ => ((1 + (x ()).re : ℝ) : ℂ)) z ξ = ξ () / 2 := by
    intro z ξ
    have : HasFDerivAt (fun x : Unit → ℂ => ((1 + (x ()).re : ℝ) : ℂ))
        (Complex.ofRealCLM.comp L) z :=
      Complex.ofRealCLM.hasFDerivAt.comp z (L.hasFDerivAt.const_add 1)
    rw [del_eq_of_hasFDerivAt this, linPart_apply]
    apply Complex.ext <;> simp [L] <;> ring
  have hl : ∀ z : Unit → ℂ, leviForm (fun x : Unit → ℂ => 1 + (x ()).re) z = 0 := by
    intro z
    have h : ContDiffAt ℂ 2 (fun x : Unit → ℂ => 1 + x ()) z :=
      contDiffAt_const.add (contDiff_apply ℂ ℂ ()).contDiffAt
    simpa using leviForm_re_eq_zero h
  have hg : ∀ ξ : Unit → ℂ, gnorm (1 : Matrix Unit Unit ℂ) ξ = ‖ξ ()‖ := by
    intro ξ
    simp [gnorm, form, dotProduct, Complex.norm_def, Complex.normSq_apply]
  refine ⟨⟨ho, fun _ _ => contDiffOn_const, fun _ _ => h1⟩, ⟨ho, fun a b => ?_, fun z _ => hp z⟩,
    hr.contDiffOn, fun z hz => Real.exp_le_exp.2 (le_add_of_nonneg_right (le_of_lt hz)),
    fun _ _ => contDiffOn_const, fun _ _ => h1.posSemidef, fun z hz v => ?_,
    fun z _ => ⟨h1, h1.posSemidef, fun ξ => ?_⟩, fun z _ => ⟨hp z, h1.posSemidef, fun ξ η => ?_⟩,
    fun z _ => ⟨h1, h1.posSemidef, fun ξ η => by simp⟩, fun z _ ξ => ?_, fun z _ => ?_⟩
  · exact ((Complex.ofRealCLM.contDiff.comp hr).mul contDiff_const).contDiffOn
  · have h0 : 0 ≤ (form (1 : Matrix Unit Unit ℂ) v v).re := by
      rw [← gnorm_sq h1.posSemidef]; positivity
    have he : 1 ≤ Real.exp (1 + (z ()).re) := Real.one_le_exp (by linarith [hz.out])
    rw [form_smul, Complex.re_ofReal_mul, Real.rpow_one]
    refine ⟨mul_le_mul_of_nonneg_right ?_ h0, le_rfl⟩
    exact (Real.rpow_le_one_of_one_le_of_nonpos he (by norm_num)).trans he
  · beta_reduce
    rw [conn_smul (H := fun _ => 1) (hr.differentiable (by simp) z) (Real.exp_pos _).ne'
      (mContDiffAt_const _) (by simp)]
    simp only [Real.log_exp, hd, add_sub_cancel_left]
    refine (opNorm_smul_le h1 h1.posSemidef _ _).trans ?_
    have h2 : opNorm (1 : Matrix Unit Unit ℂ) 1 1 ≤ 1 :=
      opNorm_le_of_bound zero_le_one fun v => by rw [hg, hg]; simp [mulVec, dotProduct]
    refine (mul_le_of_le_one_right (norm_nonneg _) h2).trans ?_
    rw [hg, norm_div]; simp
  · rw [curv_smul (H := fun _ => 1) (hr.contDiffAt.of_le (by norm_cast)) (Real.exp_pos _).ne'
      (mContDiffAt_const _) (by simp)]
    simp [hl]
  · have h2 := del_ofReal_comp (t := fun x : Unit → ℂ => 1 + (x ()).re) (z := z)
      (Real.hasDerivAt_exp _) (hu.differentiable (by simp) z) ξ
    rw [hd] at h2
    have h3 : ((Real.exp (1 + (z ()).re) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
    have h4 : -Complex.I * (gradForm (fun x : Unit → ℂ => Real.exp (1 + (x ()).re)) z ξ ξ /
        ((Real.exp (1 + (z ()).re) : ℝ) : ℂ) ^ 2) = ((‖ξ ()‖ ^ 2 / (8 * Real.pi) : ℝ) : ℂ) := by
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      rw [gradForm, dbar_ofReal, h2, kappa]
      generalize Real.exp (1 + (z ()).re) = x at h3
      push_cast
      rw [← Complex.mul_conj']
      simp only [smul_eq_mul, map_mul, Complex.conj_ofReal, map_div₀, map_ofNat]
      field_simp
      rw [Complex.I_sq]; ring
    have h5 := diagVal_formOf_eq_gnorm_sq h1.posSemidef ξ
    simp only [diagVal] at h5 ⊢
    rw [h4, Complex.ofReal_re, Complex.ofReal_one, one_mul, h5, hg]
    exact div_le_self (sq_nonneg _) (by linarith [Real.pi_gt_three])
  · rw [formAbsLe_iff]
    intro ξ
    rw [diagVal_formOf_eq_gnorm_sq h1.posSemidef]
    simp [diagVal, ddc, hl, sq_nonneg]

end GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation
