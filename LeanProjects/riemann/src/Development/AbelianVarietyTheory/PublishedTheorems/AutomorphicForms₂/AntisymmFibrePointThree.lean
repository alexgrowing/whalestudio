import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGradedLineDivisorsFullFlag

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open scoped Matrix ComplexOrder

namespace GlobalTheory.GoodMetric.Model

def fsGram (v : V 1) : Mat (fun _ : Unit => 1) ℂ := fun _ => Matrix.of fun _ _ => (((1 + ‖v‖ ^ 2)⁻¹ : ℝ) : ℂ)

theorem chernTop_fsGram (v : V 1) : chernTop (X ((), 1) ^ 1) fsGram v = (Real.pi * (1 + ‖v‖ ^ 2) ^ 2)⁻¹ := by
  have hn : ‖v 0‖ = ‖v‖ := by simp [EuclideanSpace.norm_eq]
  have hi : ‖inner ℂ v (coordVec (0 : Fin 1))‖ = ‖v‖ := by
    rw [← hn, coordVec, EuclideanSpace.inner_single_right]; simp
  have hp : 0 < 1 + ‖v‖ ^ 2 := by positivity
  have hc : ContDiffAt ℝ 2 (fun t : ℝ => (1 + t)⁻¹) (‖v‖ ^ 2) := (contDiffAt_const.add contDiffAt_id).inv hp.ne'
  have hd (t : ℝ) (h : 1 + t ≠ 0) : deriv (fun t : ℝ => Real.log (1 + t)⁻¹) t = -(1 + t)⁻¹ := by
    simp only [Real.log_inv]
    exact ((((hasDerivAt_id t).const_add 1).log h).neg.deriv).trans (by simp)
  have hd2 : deriv (deriv fun t : ℝ => Real.log (1 + t)⁻¹) (‖v‖ ^ 2) = ((1 + ‖v‖ ^ 2) ^ 2)⁻¹ := by
    have e : deriv (fun t : ℝ => Real.log (1 + t)⁻¹) =ᶠ[𝓝 (‖v‖ ^ 2)] fun t => -(1 + t)⁻¹ := by
      filter_upwards [(continuous_const.add continuous_id).continuousAt.eventually_ne hp.ne'] with t h
      exact hd t h
    rw [e.deriv_eq]
    exact ((((hasDerivAt_id _).const_add 1).inv hp.ne').neg.deriv).trans (by simp [div_eq_mul_inv])
  have hii : inner ℂ v (coordVec (0 : Fin 1)) * inner ℂ (coordVec 0) v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    rw [← inner_conj_symm (coordVec 0) v, Complex.mul_conj, Complex.normSq_eq_norm_sq, hi]
  have h1' : inner ℂ (coordVec (0 : Fin 1)) (coordVec (0 : Fin 1)) = (1 : ℂ) := by simp [coordVec]
  rw [chernTop_line, Matrix.det_unique, Matrix.of_apply,
    curv_line (f := fun x : V 1 => (1 + ‖x‖ ^ 2)⁻¹) (hc.comp (f := fun x : V 1 => ‖x‖ ^ 2) v (contDiff_norm_sq ℂ).contDiffAt)
      (inv_ne_zero hp.ne') (Eventually.of_forall fun _ => rfl), show (default : Fin 1) = 0 from rfl,
    leviForm_comp_normSq (h := fun t => Real.log (1 + t)⁻¹) (hc.log (inv_ne_zero hp.ne')), hd _ hp.ne', hd2, hii, h1',
    mul_one, ← Complex.ofReal_mul, ← Complex.ofReal_add, ← Complex.ofReal_neg, Complex.ofReal_re]
  simp only [Nat.factorial_one, Nat.cast_one, pow_one]
  field_simp
  ring

theorem integral_chernTop_fsGram : ∫ v : V 1, chernTop (X ((), 1) ^ 1) fsGram v = 1 := by
  simp only [chernTop_fsGram]
  have hr : Module.finrank ℝ (V 1) = 2 := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (V 1)]; simp
  rw [integral_fun_norm_addHaar volume (fun r : ℝ => (Real.pi * (1 + r ^ 2) ^ 2)⁻¹), Measure.real,
    InnerProductSpace.volume_ball, hr]
  have hI : ∫ y in Set.Ioi (0 : ℝ), y ^ (2 - 1) • (Real.pi * (1 + y ^ 2) ^ 2)⁻¹ = (2 * Real.pi)⁻¹ := by
    have hder : ∀ y ∈ Set.Ici (0 : ℝ), HasDerivAt (fun y : ℝ => -(2 * Real.pi)⁻¹ * (1 + y ^ 2)⁻¹)
        (y ^ (2 - 1) • (Real.pi * (1 + y ^ 2) ^ 2)⁻¹) y := fun y _ => by
      have hp : 1 + y ^ 2 ≠ 0 := by positivity
      refine ((((hasDerivAt_pow 2 y).const_add 1).inv hp).const_mul (-(2 * Real.pi)⁻¹)).congr_deriv ?_
      rw [smul_eq_mul]
      field_simp
      norm_num
    have ht : Tendsto (fun y : ℝ => -(2 * Real.pi)⁻¹ * (1 + y ^ 2)⁻¹) atTop (𝓝 0) := by
      simpa using ((tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop (α := ℝ) two_ne_zero)).inv_tendsto_atTop).const_mul
        (-(2 * Real.pi)⁻¹)
    rw [integral_Ioi_of_hasDerivAt_of_nonneg' hder (fun y hy => by have : (0 : ℝ) < y := hy; positivity) ht]
    simp
  rw [hI]
  have hg : Real.Gamma ((2 : ℕ) / 2 + 1) = 1 := by norm_num
  rw [hg, Real.sq_sqrt Real.pi_pos.le]
  simp [ENNReal.toReal_ofReal Real.pi_pos.le]

theorem antisymm_fibrePoint_three : antisymm (fibrePoint fun _ : Unit => 3) = rootDiscr fun _ : Unit => 3 := by
  classical
  have e : antisymm (fibrePoint fun _ : Unit => 3) =
      (Matrix.of fun i j : Fin 3 => (-X ⟨(), i⟩ : MvPolynomial (Root fun _ : Unit => 3) ℝ) ^ (2 - (j : ℕ))).det := by
    rw [Matrix.det_apply, antisymm]
    refine Finset.sum_equiv (Equiv.funUnique Unit _) (fun _ => by simp) fun w _ => ?_
    simp [fibrePoint, Fintype.prod_sigma, Units.smul_def]
  have h0 : Finset.Iio (0 : Fin 3) = ∅ := by decide
  have h1 : Finset.Iio (1 : Fin 3) = {0} := by decide
  have h2 : Finset.Iio (2 : Fin 3) = {0, 1} := by decide
  rw [e, Matrix.det_fin_three, rootDiscr]
  simp [Fin.prod_univ_three, h0, h1, h2]
  ring

theorem not_goodBound_normSq (c : ℝ) (N : ℕ) {v : V 1} (h0 : v ≠ 0) (h : Real.log ‖v‖ < -|c|) :
    ¬ GoodBound Finset.univ c N (fun u : V 1 => (Matrix.of fun _ _ => ((‖u‖ ^ 2 : ℝ) : ℂ) : Matrix (Fin 1) (Fin 1) ℂ)) v :=
  fun hb => by
  have hn : ‖v 0‖ = ‖v‖ := by simp [EuclideanSpace.norm_eq]
  have hp : 0 < ‖v‖ := norm_pos_iff.2 h0
  have hi : ‖inner ℂ v (coordVec (0 : Fin 1))‖ = ‖v‖ := by
    rw [← hn, coordVec, EuclideanSpace.inner_single_right]; simp
  have e : conn (fun u : V 1 => (Matrix.of fun _ _ => ((‖u‖ ^ 2 : ℝ) : ℂ) : Matrix (Fin 1) (Fin 1) ℂ)) v (coordVec 0) 0 0 =
      ((‖v‖ ^ 2 : ℝ) : ℂ)⁻¹ * inner ℂ v (coordVec 0) := by
    rw [← del_normSq]
    simp [conn, Matrix.mul_apply, mdel]
  have := hb.form 0 0 0
  rw [e, norm_mul, hi, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity), poinWt,
    if_pos (Finset.mem_univ _), hn, abs_of_neg (by linarith [abs_nonneg c])] at this
  have e2 : (‖v‖ ^ 2)⁻¹ * ‖v‖ * (‖v‖ * -Real.log ‖v‖) = -Real.log ‖v‖ := by field_simp
  linarith [le_abs_self c]

theorem not_isGood_bot {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} {m : ι → ℕ} (E : Fr (ratOf X) m 0)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (y : CxPts X.str σ) : ¬ IsGood E ⊥ H := fun h => by
  have hb (z : CxPts X.str σ) : z ∉ ptsIn X.str σ ⊥ := fun hz => mem_ptsIn.1 hz
  obtain ⟨e, S, -, hy, -, h4, -⟩ := h y (hb y)
  have hd : Dense (⋂ a : Fin X.dim, {v : V X.dim | v a ≠ 0}) := by
    refine dense_iInter_of_isOpen (fun a => isOpen_ne_fun (by fun_prop) continuous_const) fun a => ?_
    exact (dense_compl_singleton (0 : ℂ)).preimage (PiLp.isOpenMap_apply 2 _ a)
  obtain ⟨v, hv, hv'⟩ := hd.inter_open_nonempty _ e.open_target ⟨_, e.map_source hy⟩
  obtain ⟨a, -, ha⟩ := (h4 _ (e.map_target hv)).1 (hb _)
  rw [e.right_inv hv] at ha
  exact Set.mem_iInter.1 hv' a ha

theorem flagPushForward_line {F : Type} [Field F] (Y : Var F) {ι : Type} [Fintype ι] (gr : Root (fun _ : ι => 1) → Y.Dv)
    (Q : MvPolynomial (Root fun _ : ι => 1) ℝ) (R : MvPolynomial (ι × ℕ) ℝ)
    (h : antisymm Q = chernRoots (fun _ : ι => 1) R * rootDiscr fun _ : ι => 1) :
    Y.interPoly gr Q = Y.interPoly gr (chernRoots (fun _ : ι => 1) R * fibrePoint fun _ : ι => 1) := by
  classical
  have e : antisymm Q = Q := by
    rw [antisymm, Finset.sum_eq_single (fun _ => 1) (fun w _ hw => absurd (_root_.funext fun _ => Subsingleton.elim _ _) hw)
      (by simp)]
    simp only [Finset.prod_const_one, map_one, Units.val_one, one_smul]
    exact rename_id_apply Q
  have e2 : rootDiscr (fun _ : ι => 1) = 1 := by
    have h0 : Finset.Iio (0 : Fin 1) = ∅ := by decide
    simp [rootDiscr, h0]
  rw [e, e2] at h
  rw [h]
  simp [fibrePoint]

theorem volume_univ_zero : (volume : Measure (V 0)) Set.univ = 1 := by
  rw [← (stdOrthonormalBasis ℝ (V 0)).volume_parallelepiped]
  congr 1
  exact (Set.eq_univ_of_forall fun x => Subsingleton.elim 0 x ▸ ⟨0, by simp, Subsingleton.elim _ _⟩).symm

theorem exists_flagSpace {F : Type} [Field F] (X : Var F) {ι : Type} [Fintype ι] {m : ι → ℕ} (E : Fr (ratOf X) m 0) :
    ∃ (Y : Var F) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (gr : Root m → Y.Dv),
      Y.dim = X.dim + ∑ τ, (m τ).choose 2 ∧ Refines E E' φ f ∧ IsGraded E' gr := by
  obtain ⟨Y, φ, f, E', hd, hR⟩ := tower _ (ratOf X) X.dim E (good_ratOf X) (fun _ => Nat.zero_le _) rfl
  obtain ⟨B, hB⟩ := E'.nonempty (genericPoint Y.X)
  obtain ⟨gr, hgr⟩ := GlobalTheory.ShFam.GradedDiv.exists_div E' hB
  refine ⟨Y, E', φ, f, fun x => gr x.1 x.2, by simpa using hd, hR, B, hB, fun y x => ?_⟩
  obtain ⟨A, hA, t, h1, -, h3⟩ := hgr y
  exact ⟨A, hA, t x.1 x.2, h1 _ _, h3 _ _⟩

end GlobalTheory.GoodMetric.Model
