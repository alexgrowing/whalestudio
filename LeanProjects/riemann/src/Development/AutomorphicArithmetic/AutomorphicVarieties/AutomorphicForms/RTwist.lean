import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealCusp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RChar2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist

noncomputable section

open NumberField IsDedekindDomain Topology Matrix MeasureTheory Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.CuspRep Formalism.L2.Host
open scoped ContDiff

namespace UpperTheory.V.TR

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

variable (E a) in

def lieS (i j : Fin a) : Rinf E →ₗ[ℝ] Module.End ℂ (Sm E a) :=
  (lie E a).comp (Matrix.singleLinearMap ℝ i j : Rinf E →ₗ[ℝ] Matrix (Fin a) (Fin a) (Rinf E))

theorem lieS_apply (i j : Fin a) (x : Rinf E) : lieS E a i j x = lie E a (toL (Matrix.single i j x)) := rfl

theorem lieS_comm (i j k l : Fin a) (x y : Rinf E) :
    lieS E a i j x * lieS E a k l y - lieS E a k l y * lieS E a i j x =
      (if j = k then lieS E a i l (x * y) else 0) - (if l = i then lieS E a k j (x * y) else 0) := by
  simp only [lieS_apply]
  rw [lie_comm]
  congr 1
  · split_ifs with h
    · subst h; exact congrArg (fun X => lie E a (toL X)) (Matrix.single_mul_single_same _ _ _ _ _)
    · exact (congrArg (fun X => lie E a (toL X)) (Matrix.single_mul_single_of_ne _ _ _ _ h _)).trans (map_zero _)
  · split_ifs with h
    · subst h; rw [mul_comm x]; exact congrArg (fun X => lie E a (toL X)) (Matrix.single_mul_single_same _ _ _ _ _)
    · exact (congrArg (fun X => lie E a (toL X)) (Matrix.single_mul_single_of_ne _ _ _ _ h _)).trans (map_zero _)

open Classical in

theorem Eop_eq (v : InfinitePlace E) (i j : Fin a) : Eop v i j = lieS E a i j (Pi.single v 1) := rfl

theorem glRel_Eop (v : InfinitePlace E) : Formalism.REAL.GlRel (Eop (a := a) v) := by
  classical
  intro i j k l
  simp only [Eop_eq]
  rw [lieS_comm, ← Pi.single_mul, mul_one]

theorem Eop_comm {v v' : InfinitePlace E} (h : v ≠ v') (i j k l : Fin a) :
    Eop v i j * Eop v' k l = Eop v' k l * Eop v i j := by
  classical
  have e : (Pi.single v 1 : Rinf E) * Pi.single v' 1 = 0 := by
    funext w
    by_cases hw : w = v
    · subst hw; simp [Pi.single_eq_of_ne h]
    · simp [Pi.single_eq_of_ne hw]
  rw [← sub_eq_zero]
  simp only [Eop_eq]
  rw [lieS_comm, e]
  simp

theorem cap_comm (τ : InfinitePlace E) (u : ℂ) (i j : Fin a) : cap τ u * Eop τ i j = Eop τ i j * cap τ u :=
  Formalism.REAL.qDetCentral _ a _ (glRel_Eop τ) _ i j

theorem cap_highest (τ : InfinitePlace E) (ν : Fin a → ℂ) (φ : Sm E a) (h : Formalism.REAL.IsHW (Eop τ) ν φ) (u : ℂ) :
    cap τ u φ = (∏ k : Fin a, (u + (ν k + (((a : ℂ) - 1) / 2 - (k : ℕ))))) • φ := by
  rw [cap, Formalism.REAL.qDetHW _ a _ ν φ (glRel_Eop τ) h]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by ring

theorem det_finGL (k : GL (Fin a) (Af E)) :
    GeneralLinearGroup.det (finGL E a k) = finId E (GeneralLinearGroup.det k) := by
  refine Units.ext (ad_ext ?_ ?_)
  · rw [← GlobalTheory.CuspRep.det_map, pInf_finGL]
    change _ = pInf E (1 - sFin E 1 + sFin E _)
    have h : ∀ x, pInf E (sFin E x) = 0 := fun x => map_zero (infEq E).symm
    simp [h]
  · rw [← GlobalTheory.CuspRep.det_map, pFin_finGL]
    change _ = (1 : Af E) - 1 + (GeneralLinearGroup.det k : (Af E)ˣ)
    simp

def chiInf (χ : HChar E) : (Rinf E)ˣ →* ℂˣ := χ.1.comp (infId E)

theorem continuous_chiInf (χ : HChar E) : Continuous (chiInf χ) := χ.2.1.comp (continuous_infId E)

def dchi (χ : HChar E) : Rinf E →L[ℝ] ℂ := fderiv ℝ (extZero (chiInf χ)) 1

theorem chiInf_expU (χ : HChar E) (z : Rinf E) : ((chiInf χ (expU z) : ℂˣ) : ℂ) = Complex.exp (dchi χ z) := by
  obtain ⟨L, hL⟩ := exists_lin _ (continuous_chiInf χ)
  rw [dchi, fderiv_extZero (continuous_chiInf χ) hL, hL]

theorem dchi_eq_of_exp (χ : HChar E) (d : Rinf E →ₗ[ℝ] ℂ)
    (h : ∀ z, ((chiInf χ (expU z) : ℂˣ) : ℂ) = Complex.exp (d z)) (z : Rinf E) : dchi χ z = d z := by
  rw [dchi, fderiv_extZero (L := LinearMap.toContinuousLinearMap d) (continuous_chiInf χ) h]
  rfl

open Classical in

def expo (χ : HChar E) (v : InfinitePlace E) : ℂ := dchi χ (Pi.single v 1)

theorem dchi_eq_sum (χ : HChar E) (z : Rinf E) : dchi χ z = ∑ v, expo χ v * (z v : ℂ) := by
  classical
  conv_lhs => rw [pi_eq_sum_univ' z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_smul, Complex.real_smul, mul_comm]
  rfl

theorem chiInf_expU_eq (χ : HChar E) (z : Rinf E) :
    ((chiInf χ (expU z) : ℂˣ) : ℂ) = Complex.exp (∑ v, expo χ v * (z v : ℂ)) := by
  rw [chiInf_expU, dchi_eq_sum]

open Classical in

theorem expo_eq_of_exp (χ : HChar E) (v : InfinitePlace E) (p : ℂ)
    (h : ∀ t : ℝ, ((chiInf χ (expU (Pi.single v t)) : ℂˣ) : ℂ) = Complex.exp (p * t)) : expo χ v = p := by
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp (t * expo χ v)) (expo χ v) 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (expo χ v)).cexp
  have h2 : HasDerivAt (fun t : ℝ => Complex.exp (t * p)) p 0 := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const p).cexp
  refine h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_))
  have e : (Pi.single v t : Rinf E) = t • (Pi.single v 1 : Rinf E) := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have := h t
  rw [chiInf_expU, e, map_smul, Complex.real_smul, mul_comm p] at this
  exact this

theorem dchi_mul (χ χ' : HChar E) (z : Rinf E) : dchi (χ * χ') z = dchi χ z + dchi χ' z :=
  dchi_eq_of_exp (χ * χ') ((dchi χ).toLinearMap + (dchi χ').toLinearMap) (fun z => by
    change ((chiInf χ (expU z) * chiInf χ' (expU z) : ℂˣ) : ℂ) = Complex.exp (dchi χ z + dchi χ' z)
    rw [Units.val_mul, chiInf_expU, chiInf_expU, Complex.exp_add]) z

theorem dchi_one (z : Rinf E) : dchi (1 : HChar E) z = 0 :=
  dchi_eq_of_exp 1 0 (fun z => by simp [chiInf]) z

theorem dchi_inv (χ : HChar E) (z : Rinf E) : dchi χ⁻¹ z = -dchi χ z :=
  eq_neg_of_add_eq_zero_left (by rw [← dchi_mul, inv_mul_cancel, dchi_one])

theorem expo_mul (χ χ' : HChar E) (v : InfinitePlace E) : expo (χ * χ') v = expo χ v + expo χ' v := dchi_mul _ _ _

theorem expo_one (v : InfinitePlace E) : expo (1 : HChar E) v = 0 := dchi_one _

theorem expo_inv (χ : HChar E) (v : InfinitePlace E) : expo χ⁻¹ v = -expo χ v := dchi_inv _ _

theorem chart_mul_chi (χ : HChar E) (φ : GA E a → ℂ) (g : GA E a) :
    chart (fun x => φ x * (chiDet a χ x : ℂˣ)) g =
      fun x => chart φ g x * ((chiDet a χ g : ℂˣ) * extZero (chiInf χ) (Matrix.of x).det) := by
  funext x
  by_cases h : IsUnit (Matrix.of x)
  · obtain ⟨u, hu⟩ := h
    have hx : x = toL u.val := hu.symm
    rw [hx, chart_val, chart_val, map_mul, Units.val_mul]
    congr 2
    rw [show chiDet a χ (infGL E a u) = chiInf χ (GeneralLinearGroup.det u) from congrArg χ.1 (det_infGL u)]
    exact (extZero_unit _ _).symm
  · simp [chart, h]

theorem contDiffAt_chi_det (χ : HChar E) {x : Lie E a} (hx : x ∈ invSet E a) :
    ContDiffAt ℝ ∞ (fun x : Lie E a => extZero (chiInf χ) (Matrix.of x).det) x := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hx
  exact ContDiffAt.comp (g := extZero (chiInf χ)) x (hu ▸ contDiffAt_extZero _ (continuous_chiInf χ) u)
    contDiff_det.contDiffAt

theorem mul_chi_mem_Sm (χ : HChar E) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) :
    (fun x => φ x * (chiDet a χ x : ℂˣ)) ∈ Sm E a := fun g => by
  rw [chart_mul_chi]
  exact (hφ g).mul (contDiffOn_const.mul fun x hx => (contDiffAt_chi_det χ hx).contDiffWithinAt)

variable (a) in

def mulChi (χ : HChar E) : Sm E a ≃ₗ[ℂ] Sm E a where
  toFun φ := ⟨fun x => φ.1 x * (chiDet a χ x : ℂˣ), mul_chi_mem_Sm χ φ.2⟩
  invFun φ := ⟨fun x => φ.1 x * (chiDet a χ⁻¹ x : ℂˣ), mul_chi_mem_Sm χ⁻¹ φ.2⟩
  map_add' φ ψ := Subtype.ext <| funext fun x => add_mul _ _ _
  map_smul' c φ := Subtype.ext <| funext fun x => mul_assoc _ _ _
  left_inv φ := Subtype.ext <| funext fun x => Units.mul_inv_cancel_right _ _
  right_inv φ := Subtype.ext <| funext fun x => Units.inv_mul_cancel_right _ _

@[simp] theorem mulChi_apply (χ : HChar E) (φ : Sm E a) (g : GA E a) :
    (mulChi a χ φ).1 g = φ.1 g * (chiDet a χ g : ℂˣ) := rfl

theorem mulChi_mul (χ χ' : HChar E) (φ : Sm E a) : mulChi a (χ * χ') φ = mulChi a χ' (mulChi a χ φ) :=
  Subtype.ext <| funext fun _ => (mul_assoc _ _ _).symm

theorem mulChi_one (φ : Sm E a) : mulChi a 1 φ = φ := Subtype.ext <| funext fun _ => mul_one _

theorem rt_mulChi (χ : HChar E) (h : GA E a) (φ : Sm E a) :
    rt E a h (mulChi a χ φ) = mulChi a χ (((chiDet a χ h : ℂˣ) : ℂ) • rt E a h φ) :=
  Subtype.ext <| funext fun g => by
    simp only [rt_apply, mulChi_apply, map_mul, Units.val_mul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]; ring

omit [IsTotallyReal E] in

theorem fderiv_det_one (X : Lie E a) :
    fderiv ℝ (fun x : Lie E a => (Matrix.of x).det) (oneL E a) X = (Matrix.of X).trace := by
  have hd : HasFDerivAt (fun x : Lie E a => (Matrix.of x).det)
      (fderiv ℝ (fun x : Lie E a => (Matrix.of x).det) (oneL E a)) (oneL E a + (0 : ℝ) • X) := by
    rw [zero_smul, add_zero]
    exact (contDiff_det.differentiable (by simp) _).hasFDerivAt
  have h1 := hd.comp_hasDerivAt (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (oneL E a))
  rw [one_smul] at h1
  refine h1.unique ?_
  set P := (1 + (Polynomial.X : Polynomial (Rinf E)) • (Matrix.of X).map Polynomial.C).det.divX.divX
  have hr : HasDerivAt (fun t : ℝ => t • (1 : Rinf E)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (1 : Rinf E)
  have hP : DifferentiableAt ℝ (fun t : ℝ => P.eval (t • (1 : Rinf E))) 0 := by
    simp only [Polynomial.eval_eq_sum_range]
    fun_prop
  have h2 := ((hr.const_mul (Matrix.of X).trace).const_add 1).add (hP.hasDerivAt.mul (hr.mul hr))
  simp only [mul_one, zero_smul, Pi.mul_apply, mul_zero, zero_mul, add_zero] at h2
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have e : Matrix.of (oneL E a + t • X) = 1 + (t • (1 : Rinf E)) • Matrix.of X := by
    rw [smul_assoc, one_smul]; rfl
  change (Matrix.of (oneL E a + t • X)).det = _
  rw [e, Matrix.det_one_add_smul, sq]
  rfl

theorem lie_mulChi (χ : HChar E) (X : Lie E a) (φ : Sm E a) :
    lie E a X (mulChi a χ φ) = mulChi a χ (lie E a X φ + dchi χ (Matrix.of X).trace • φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have h1 : (Matrix.of (oneL E a)).det = 1 := Matrix.det_one
  have hd : HasFDerivAt (fun x : Lie E a => extZero (chiInf χ) (Matrix.of x).det)
      ((dchi χ).comp (fderiv ℝ (fun x : Lie E a => (Matrix.of x).det) (oneL E a))) (oneL E a) := by
    refine HasFDerivAt.comp (g := extZero (chiInf χ)) _ ?_ (contDiff_det.differentiable (by simp) _).hasFDerivAt
    rw [h1]
    exact ((contDiffAt_extZero _ (continuous_chiInf χ) 1).differentiableAt (by simp)).hasFDerivAt
  have h2 := ((differentiableAt_chart φ.2 g).hasFDerivAt.mul (hd.const_mul ((chiDet a χ g : ℂˣ) : ℂ))).fderiv
  have h3 : extZero (chiInf χ) 1 = 1 := (extZero_unit _ 1).trans (by simp)
  have h4 : chart φ.1 g (oneL E a) = φ.1 g := (chart_val φ.1 g 1).trans (by simp)
  change fderiv ℝ (chart (fun x => φ.1 x * (chiDet a χ x : ℂˣ)) g) _ X = (lieD X φ.1 g + _ * φ.1 g) * _
  rw [chart_mul_chi]
  refine (congrArg (fun L : Lie E a →L[ℝ] ℂ => L X) h2).trans ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    fderiv_det_one, h1, h3, h4, smul_eq_mul, lieD]
  ring

theorem Eop_mulChi (χ : HChar E) (τ : InfinitePlace E) (i j : Fin a) (φ : Sm E a) :
    Eop τ i j (mulChi a χ φ) = mulChi a χ (Eop τ i j φ + (if i = j then expo χ τ else 0) • φ) := by
  have ht : ∀ x : Rinf E, (Matrix.of (toL (Matrix.single i j x))).trace = if i = j then x else 0 := fun x => by
    change (Matrix.single i j x).trace = _
    split_ifs with h
    · subst h; simp
    · exact Matrix.trace_single_eq_of_ne _ _ _ h
  simp only [Eop, lie_mulChi, ht]
  congr 1
  split_ifs
  · rfl
  · simp

theorem cap_mulChi (χ : HChar E) (τ : InfinitePlace E) (u : ℂ) (φ : Sm E a) :
    cap τ u (mulChi a χ φ) = mulChi a χ (cap τ (u + expo χ τ) φ) := by
  have h := map_qdet ((mulChi a χ).conjAlgEquiv ℂ).toAlgHom
    (fun i j => Eop τ i j + if i = j then algebraMap ℂ _ (expo χ τ) else 0) (u + ((a : ℂ) - 1) / 2)
  have e : (fun i j => ((mulChi a χ).conjAlgEquiv ℂ).toAlgHom
      (Eop τ i j + if i = j then algebraMap ℂ _ (expo χ τ) else 0)) = Eop τ := by
    funext i j
    refine LinearMap.ext fun ψ => ?_
    obtain ⟨ψ, rfl⟩ := (mulChi a χ).surjective ψ
    rw [Eop_mulChi]
    change mulChi a χ ((Eop τ i j + if i = j then algebraMap ℂ _ (expo χ τ) else 0)
      ((mulChi a χ).symm (mulChi a χ ψ))) = _
    rw [LinearEquiv.symm_apply_apply]
    split_ifs <;> simp
  rw [e, qdet_shift] at h
  rw [cap, ← h, cap, add_right_comm u (expo χ τ)]
  generalize Formalism.REAL.qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2 + expo χ τ) = z
  change mulChi a χ (z ((mulChi a χ).symm (mulChi a χ φ))) = _
  rw [LinearEquiv.symm_apply_apply]

def opMul (χ : HChar E) : Op E a → ℂˣ
  | .fin k => chiDet a χ (finGL E a k)
  | .cpt k => chiDet a χ (infGL E a (Unitary.toUnits k))
  | .lie _ => 1

def opAdd (χ : HChar E) : Op E a → ℂ
  | .fin _ => 0
  | .cpt _ => 0
  | .lie X => dchi χ (Matrix.of X).trace

theorem act_mulChi (χ : HChar E) (o : Op E a) (φ : Sm E a) :
    act o (mulChi a χ φ) = mulChi a χ (((opMul χ o : ℂˣ) : ℂ) • act o φ + opAdd χ o • φ) := by
  cases o with
  | fin k => simp only [opAdd, zero_smul, add_zero]; exact rt_mulChi χ (finGL E a k) φ
  | cpt k => simp only [opAdd, zero_smul, add_zero]; exact rt_mulChi χ (infGL E a (Unitary.toUnits k)) φ
  | lie X => simp only [opMul, Units.val_one, one_smul]; exact lie_mulChi χ X φ

theorem isOpen_ker_chiDet (χ : HChar E) : IsOpen {k : GL (Fin a) (Af E) | chiDet a χ (finGL E a k) = 1} := by
  have h := (isOpen_ker_finIdele E (χ.1.comp (finId E)) (χ.2.1.comp (continuous_finId E))).preimage
    (GeneralLinearGroup.continuous_det (n := Fin a))
  convert h using 1
  ext k
  exact Iff.of_eq (congrArg (fun u => χ.1 u = 1) (det_finGL k))

omit [IsTotallyReal E] in

theorem one_le_height (y : GL (Fin a) (Rinf E)) : 1 ≤ height y := by
  unfold height; linarith [norm_nonneg (toL y.val), norm_nonneg (toL (y⁻¹).val)]

omit [IsTotallyReal E] in

theorem norm_det_le (x : Matrix (Fin a) (Fin a) (Rinf E)) {B : ℝ} (hx : ‖toL x‖ ≤ B) :
    ‖x.det‖ ≤ a.factorial * B ^ a := by
  rw [Matrix.det_apply]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (B ^ a) fun σ _ => ?_).trans_eq
    (by simp [Fintype.card_perm]))
  have h : ‖∏ i, x (σ i) i‖ ≤ B ^ a := by
    refine (Finset.norm_prod_le _ _).trans ((Finset.prod_le_prod (g := fun _ => B) (fun _ _ => norm_nonneg _)
      fun i _ => ?_).trans_eq (by simp))
    exact ((norm_le_pi_norm (toL x (σ i)) i).trans (norm_le_pi_norm (toL x) (σ i))).trans hx
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simpa [e] using h

theorem chiDet_growth (χ : HChar E) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖((chiDet a χ (infGL E a y) : ℂˣ) : ℂ)‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, -, h⟩ := exists_bound _ (continuous_chiInf χ)
  refine ⟨C * a.factorial ^ N, a * N, fun y => ?_⟩
  have h1 := one_le_height y
  have h2 := h (GeneralLinearGroup.det y) (a.factorial * height y ^ a)
    (one_le_mul_of_one_le_of_one_le (by exact_mod_cast a.factorial_pos) (one_le_pow₀ h1))
    (norm_det_le _ (by unfold height; linarith [norm_nonneg (toL (y⁻¹).val)]))
    (by rw [← map_inv]; exact norm_det_le _ (by unfold height; linarith [norm_nonneg (toL y.val)]))
  rw [show chiDet a χ (infGL E a y) = chiInf χ (GeneralLinearGroup.det y) from congrArg χ.1 (det_infGL y)]
  exact h2.trans_eq (by rw [mul_pow, ← pow_mul, mul_assoc])

theorem Zalg_mulChi (χ : HChar E) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg E a, ∀ φ, z (mulChi a χ φ) = mulChi a χ (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨_, Algebra.subset_adjoin ⟨τ, _, rfl⟩, cap_mulChi χ τ u⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩

theorem IsAutForm.mulChi {φ : Sm E a} (h : IsAutForm φ) (χ : HChar E) : IsAutForm (mulChi a χ φ) where
  left γ g := by simp [h.left, chiDet_ratGL]
  level := isOpen_stab_of_mem_nhds _ _ <| Filter.mem_of_superset
    ((h.level.inter (isOpen_ker_chiDet χ)).mem_nhds ⟨by simp, by simp⟩) fun k hk => by
      have h1 : rt E a (finGL E a k) φ = φ := hk.1
      have h2 : chiDet a χ (finGL E a k) = 1 := hk.2
      change rt E a (finGL E a k) _ = _
      rw [rt_mulChi, h1, h2, Units.val_one, one_smul]
  kfin := by
    have := h.kfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
      (TR.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨_, Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩), (rt_mulChi χ _ φ).symm⟩
  zfin := by
    have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map (TR.mulChi a χ).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_mulChi χ hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth g
    obtain ⟨C', N', h2⟩ := chiDet_growth (a := a) χ
    refine ⟨C * (‖((chiDet a χ g : ℂˣ) : ℂ)‖ * C'), N + N', fun y => ?_⟩
    rw [mulChi_apply, map_mul, Units.val_mul, norm_mul, norm_mul]
    refine (mul_le_mul (h1 y) (mul_le_mul_of_nonneg_left (h2 y) (norm_nonneg _)) (by positivity)
      ((norm_nonneg _).trans (h1 y))).trans_eq ?_
    ring

theorem IsCuspForm.mulChi {φ : Sm E a} (h : IsCuspForm φ) (χ : HChar E) : IsCuspForm (mulChi a χ φ) := by
  refine ⟨h.1.mulChi χ, fun r h0 h1 _ _ μ 𝓕 hμ hF g => ?_⟩
  have e : ∀ x : BlockIx a r → Ad E, chiDet a χ (unip x * g) = chiDet a χ g := fun x => by
    rw [map_mul, show chiDet a χ (unip x) = 1 from (congrArg χ.1 (det_unip x)).trans (map_one _), one_mul]
  simp only [mulChi_apply, e]
  rw [integral_mul_const, h.2 r h0 h1 μ 𝓕 hμ hF g, zero_mul]

namespace CuspSub

variable (π π' : CuspSub E a)

theorem Iso.refl : Iso π π := ⟨.refl _ _, fun _ _ => rfl⟩

variable {π π'} in
theorem Iso.symm (h : Iso π π') : Iso π' π :=
  h.elim fun T h => ⟨T.symm, fun o φ => T.injective (by rw [h]; simp)⟩

variable {π π'} in
theorem Iso.trans {π'' : CuspSub E a} (h : Iso π π') (h' : Iso π' π'') : Iso π π'' :=
  h.elim fun T h => h'.elim fun T' h' => ⟨T.trans T', fun o φ => by simp [h, h']⟩

variable (E a) in

instance setoid : Setoid (CuspSub E a) where
  r := Iso
  iseqv := ⟨Iso.refl, Iso.symm, Iso.trans⟩

def twist (χ : HChar E) : CuspSub E a where
  V := π.V.map (mulChi a χ).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact (π.cusp φ hφ).mulChi χ
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, add_mem (π.V.smul_mem _ (π.stable o φ hφ)) (π.V.smul_mem _ hφ), (act_mulChi χ o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := mulChi a χ)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (mulChi a χ).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (mulChi a χ).injective h2]) fun o φ hφ => by
      have h1 : _ ∈ W.comap (mulChi a χ).toLinearMap := (act_mulChi χ o φ) ▸ hs o _ hφ
      exact (Submodule.smul_mem_iff _ (Units.ne_zero (opMul χ o))).1
        ((Submodule.add_mem_iff_left _ (Submodule.smul_mem _ _ hφ)).1 h1)
    have e := Submodule.map_comap_eq_of_surjective (f := (mulChi a χ).toLinearMap) (mulChi a χ).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

def toTwist (χ : HChar E) : π.V ≃ₗ[ℂ] (π.twist χ).V := (mulChi a χ).submoduleMap π.V

theorem op_toTwist (χ : HChar E) (o : Op E a) (φ : π.V) :
    (π.twist χ).op o (π.toTwist χ φ) = π.toTwist χ (((opMul χ o : ℂˣ) : ℂ) • π.op o φ + opAdd χ o • φ) :=
  Subtype.ext (act_mulChi χ o φ.1)

variable {π π'} in

theorem Iso.twist (h : Iso π π') (χ : HChar E) : Iso (π.twist χ) (π'.twist χ) := by
  obtain ⟨T, hT⟩ := h
  refine ⟨((π.toTwist χ).symm.trans T).trans (π'.toTwist χ), fun o φ => ?_⟩
  obtain ⟨φ, rfl⟩ := (π.toTwist χ).surjective φ
  simp only [op_toTwist, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, map_add T, map_smul T, hT]

theorem twist_one : π.twist 1 = π := CuspSub.ext <| by
  ext φ
  exact ⟨fun ⟨ψ, h, e⟩ => e ▸ (mulChi_one ψ).symm ▸ h, fun h => ⟨φ, h, mulChi_one φ⟩⟩

theorem twist_mul (χ χ' : HChar E) : π.twist (χ * χ') = (π.twist χ).twist χ' := CuspSub.ext <| by
  change _ = (π.V.map _).map _
  rw [← Submodule.map_comp]
  exact congrArg (fun f => π.V.map f) (LinearMap.ext (mulChi_mul χ χ'))

variable {π π'}

theorem HasInfChar.unique {τ : InfinitePlace E} {m m' : Multiset ℂ} (h : π.HasInfChar τ m) (h' : π.HasInfChar τ m') :
    m = m' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have e : (( m.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((m'.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod := by
    refine Polynomial.funext fun u => ?_
    have := smul_left_injective ℂ h0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map] using this
  have e2 := congrArg Polynomial.roots e
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  exact Multiset.map_injective neg_injective e2

theorem iso_cap (T : π.V ≃ₗ[ℂ] π'.V) (hT : ∀ o φ, T (π.op o φ) = π'.op o (T φ)) (τ : InfinitePlace E) (u : ℂ) (φ : π.V) :
    ∃ h : cap τ u φ.1 ∈ π.V, (T ⟨_, h⟩).1 = cap τ u (T φ).1 := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ φ : π.V, ∃ h : z φ.1 ∈ π.V, (T ⟨_, h⟩).1 = z (T φ).1}
      mul_mem' := fun {x y} hx hy φ => by
        obtain ⟨h1, e1⟩ := hy φ
        obtain ⟨h2, e2⟩ := hx ⟨_, h1⟩
        exact ⟨h2, e2.trans (congrArg x e1)⟩
      add_mem' := fun {x y} hx hy φ => by
        obtain ⟨h1, e1⟩ := hx φ
        obtain ⟨h2, e2⟩ := hy φ
        exact ⟨add_mem h1 h2, (congrArg Subtype.val (map_add T ⟨_, h1⟩ ⟨_, h2⟩)).trans (congrArg₂ (· + ·) e1 e2)⟩
      algebraMap_mem' := fun c φ => ⟨π.V.smul_mem c φ.2, congrArg Subtype.val (map_smul T c φ)⟩ }
  have hL : ∀ X, lie E a X ∈ S := fun X φ => ⟨π.stable (.lie X) _ φ.2, congrArg Subtype.val (hT (.lie X) φ)⟩
  have hE : ∀ i j, Eop τ i j ∈ S := fun i j => hL _
  have : cap τ u ∈ S := by
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact this φ

theorem Iso.hasInfChar (h : Iso π π') {τ : InfinitePlace E} {m : Multiset ℂ} (hm : π.HasInfChar τ m) : π'.HasInfChar τ m := by
  obtain ⟨T, hT⟩ := h
  refine ⟨hm.1, fun u φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := T.surjective ⟨φ, hφ⟩
  obtain ⟨h1, e⟩ := iso_cap T hT τ u ψ
  have e2 : (⟨_, h1⟩ : π.V) = (m.map (u + ·)).prod • ψ := Subtype.ext (hm.2 u _ ψ.2)
  rw [e2, map_smul, hψ] at e
  exact e.symm

theorem HasInfChar.twist {τ : InfinitePlace E} {m : Multiset ℂ} (h : π.HasInfChar τ m) (χ : HChar E) :
    (π.twist χ).HasInfChar τ (m.map (· + expo χ τ)) := by
  refine ⟨by rw [Multiset.card_map, h.1], ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (mulChi a χ φ) = _ • mulChi a χ φ
  rw [cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]
  congr 3
  funext z
  simp only [Function.comp_apply]; ring

theorem Iso.isRegAlg (h : Iso π π') (hπ : π.IsRegAlg) : π'.IsRegAlg := fun v =>
  (hπ v).imp fun _ hm => ⟨h.hasInfChar hm.1, hm.2⟩

theorem IsRegAlg.twist (h : π.IsRegAlg) {χ : HChar E} (hχ : ∀ v, ∃ n : ℤ, expo χ v = n) : (π.twist χ).IsRegAlg := fun v => by
  obtain ⟨m, h1, h2, h3⟩ := h v
  obtain ⟨n, hn⟩ := hχ v
  refine ⟨_, h1.twist χ, h2.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := h3 y hy
  exact ⟨k + n, by rw [hn]; push_cast; ring⟩

theorem finPart_eq (k : GL (Fin a) (Af E)) : π.finPart k = π.op (.fin k) := rfl

theorem locRep_eq (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    π.locRep w g = π.op (.fin (locGL E a w g)) := rfl

variable (π) in

theorem isSmooth_finPart : GlobalTheory.PRep.IsSmooth π.finPart := fun φ => by
  convert (π.cusp _ φ.2).1.level using 1
  ext k
  exact Subtype.ext_iff

variable (π) in

theorem isSmooth_locRep (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.PRep.IsSmooth (π.locRep w) := fun φ =>
  (π.isSmooth_finPart φ).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)

theorem IsLocComp.congr {w : HeightOneSpectrum (𝓞 E)} {σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (h : π.IsLocComp w σ) (hπ : Iso π π') (hσ : Nonempty (σ.ρ.Equiv σ'.ρ)) : π'.IsLocComp w σ' := by
  obtain ⟨f, h0, hf⟩ := h
  obtain ⟨T, hT⟩ := hπ
  obtain ⟨e⟩ := hσ
  refine ⟨T.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearEquiv.toLinearMap, fun h => h0 (LinearMap.ext fun v => T.injective ?_),
    fun g v => ?_⟩
  · have := LinearMap.congr_fun h (e.toLinearEquiv v)
    rw [LinearMap.zero_apply, map_zero]
    exact (congrArg (fun x => T (f x)) (e.toLinearEquiv.symm_apply_apply v)).symm.trans this
  · have h1 : e.symm.toLinearEquiv (σ'.ρ g v) = σ.ρ g (e.symm.toLinearEquiv v) :=
      LinearMap.congr_fun (e.symm.isIntertwining' g) v
    change T (f (e.symm.toLinearEquiv (σ'.ρ g v))) = π'.locRep w g (T (f (e.symm.toLinearEquiv v)))
    rw [h1, hf, locRep_eq, hT, locRep_eq]

theorem chiDet_locGL (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    chiDet a χ (finGL E a (locGL E a w g)) = GlobalTheory.CuspRep.CuspSub.locDet a χ w g :=
  congrArg χ.1 ((det_finGL _).trans (finId_det_locGL w g))

theorem isOpen_ker_locDet (χ : HChar E) (w : HeightOneSpectrum (𝓞 E)) : IsOpen {g | GlobalTheory.CuspRep.CuspSub.locDet a χ w g = 1} := by
  simpa only [Set.preimage_ofPred_eq, chiDet_locGL] using (isOpen_ker_chiDet (a := a) χ).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)

theorem IsLocComp.twist {w : HeightOneSpectrum (𝓞 E)} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (h : π.IsLocComp w σ) (χ : HChar E) :
    (π.twist χ).IsLocComp w (σ.twist (GlobalTheory.CuspRep.CuspSub.locDet a χ w) (isOpen_ker_locDet χ w)) := by
  obtain ⟨f, h0, hf⟩ := h
  refine ⟨(π.toTwist χ).toLinearMap ∘ₗ f, fun h => h0 (LinearMap.ext fun v => (π.toTwist χ).injective ?_), fun g v => ?_⟩
  · rw [LinearMap.zero_apply, map_zero]; exact LinearMap.congr_fun h v
  · change π.toTwist χ (f (((GlobalTheory.CuspRep.CuspSub.locDet a χ w g : ℂˣ) : ℂ) • σ.ρ g v)) =
      (π.twist χ).op (.fin (locGL E a w g)) (π.toTwist χ (f v))
    rw [op_toTwist, map_smul f, hf g v, ← chiDet_locGL, opAdd, zero_smul, add_zero]
    rfl

theorem finPart_toTwist (χ : HChar E) (k : GL (Fin a) (Af E)) (φ : π.V) :
    (π.twist χ).finPart k (π.toTwist χ φ) = ((chiDet a χ (finGL E a k) : ℂˣ) : ℂ) • π.toTwist χ (π.finPart k φ) := by
  rw [finPart_eq, op_toTwist, opAdd, zero_smul, add_zero, map_smul]
  rfl

theorem Iso.hasSat (h : Iso π π') {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (hB : π.HasSat w B) : π'.HasSat w B := by
  obtain ⟨T, hT⟩ := h
  have hf : ∀ g y, T.toLinearMap (π.locRep w g y) = π'.locRep w g (T.toLinearMap y) := fun g y => hT (.fin _) y
  constructor
  · obtain ⟨x, hx⟩ := hB.exists_vec
    have h1 := hx.map T.toLinearMap hf ((map_ne_zero_iff T T.injective).2 hx.1)
    exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine (hB.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) fun e => h0 (by rw [e, map_zero])).map
      T.toLinearMap hf h0
    exact (hf k x).trans (GlobalTheory.LGrp.mem_fixed.1 hy k hk)

theorem HasSat.unique {w : HeightOneSpectrum (𝓞 E)} {B B' : Multiset ℂˣ} (h : π.HasSat w B) (h' : π.HasSat w B') :
    B = B' := GlobalTheory.LFun.HasSatGL.unique h h'

theorem HasSat.card {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B) : B.card = a :=
  GlobalTheory.LFun.HasSatGL.card h

theorem HasSat.twist {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B) {χ : HChar E} (hχ : χ.UnrAt w) :
    (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  refine GlobalTheory.SphGal.hasSatGL_of_twist hχ (π.toTwist χ) (fun g x => ?_) h
  rw [locRep_eq, op_toTwist, opAdd, zero_smul, add_zero, map_smul, opMul, chiDet_locGL]
  rfl

end CuspSub

end UpperTheory.V.TR
