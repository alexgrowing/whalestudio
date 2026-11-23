import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH

namespace GlobalTheory.PoinHol

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem differentiable_lact (X : Data E r) (γ : GL (Fin r) E) :
    Differentiable ℂ fun x : Frame X.Ψ r => lact γ x := by
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun c => ?_
  have e : (fun x : Frame X.Ψ r => lact γ x τ a c) = fun x =>
      ∑ d, (γ : Matrix (Fin r) (Fin r) E).map τ.1 a d * x τ d c := by
    funext z
    rfl
  rw [e]
  exact Differentiable.fun_sum fun d _ => (differentiable_const _).mul (by fun_prop)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem isOrth_lact_of_isOrth {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x) : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hx ⊢
  intro τ
  rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.gram_lact X hγ]
  exact hx τ

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem continuousAt_bchar_of_ne_zero (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hb : _root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b ≠ 0) :
    ContinuousAt (fun c : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => _root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la c) b := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.bchar at hb ⊢
  refine tendsto_finset_prod _ fun τ _ => tendsto_finset_prod _ fun i _ => ?_
  have hne : b τ i i ≠ 0 ∨ 0 ≤ la τ i := by
    by_cases h0 : la τ i = 0
    · exact Or.inr h0.ge
    · left
      intro hz
      apply hb
      refine Finset.prod_eq_zero (Finset.mem_univ τ) (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
      rw [hz, zero_zpow _ h0]
  have hc : Continuous fun c : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => c τ i i :=
    (continuous_apply i).comp ((continuous_apply i).comp (continuous_apply τ))
  exact hc.continuousAt.zpow₀ _ hne

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem bchar_ne_zero_of_mem_bor_torus_haar_measure (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    {b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hb : b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r) : _root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b ≠ 0 := by
  intro h
  have hmul := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.bchar_mul X la hb (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem X hb)
  rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_invF X hb, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.bchar_oneF X la, h, zero_mul] at hmul
  exact one_ne_zero hmul

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem rmul_lact_comm {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ : GL (Fin r) E)
    (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) : _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) b = _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul _root_.ReciprocityTheory.ChartRestriction.G.FD.lact
  funext τ
  exact Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)
    (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ)

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem cpt_lact_eq_lact_cpt {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ : GL (Fin r) E)
    (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) :
    _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) z = _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt
  exact rmul_lact_comm X γ x _

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private theorem norm_chi_eq_one_of_mem_gamma {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have hpow : ‖X.χ la γ‖ ^ n = 1 := by rw [← norm_pow, h γ hγ, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 hpow

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem differentiable_lact' (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ : GL (Fin r) E) :
    Differentiable ℂ (fun x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r => _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) := by
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.FD.lact, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem lact_lact_eq_lact_mul' (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (γ δ : GL (Fin r) E) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact δ x) = _root_.ReciprocityTheory.ChartRestriction.G.FD.lact (γ * δ) x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.lact
  funext τ
  show ((γ : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)) *
      (((δ : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) =
      (((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ
  rw [← Matrix.mul_assoc, ← Matrix.map_mul, Units.val_mul]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in
private theorem lact_one_apply (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.lact (1 : GL (Fin r) E) x = x := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.lact
  funext τ
  show (((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map (τ : E →+* ℂ)) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} in

theorem _root_.GlobalTheory.PoinHol.poin_summable_isBddSec :
    (∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (ι : Type) (U : Set H) (f : ι → H → ℂ) (u : ι → ℝ), IsOpen U → (∀ i, DifferentiableOn ℂ (f i) U) → Summable u → (∀ i, ∀ x ∈ U, ‖f i x‖ ≤ u i) → DifferentiableOn ℂ (fun x => ∑' i, f i x) U) → (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacRmulStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.NfacLactStatement (E := E) ∧ _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.PnormInvStatement (E := E)) → (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (κ : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℝ) (P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P → (∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 x))) ≤ C) → (∃ ρ C : ℝ, 0 < ρ ∧ ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ < ρ → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom ∧ ‖P (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z)‖ ≤ C * Real.sqrt (κ x)) → (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 x)‖) ∧ X.IsBddSec la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P)) := by
  intro hWeier hstat r X la κ P hP hκsum hloc
  have hPnorm := hstat.2.2
  obtain ⟨ρ, C, hρ, hl⟩ := hloc
  obtain ⟨C₁, hC₁, hC₁b⟩ := hκsum
  have hsq : ∀ x ∈ X.dom, Summable (fun γ : X.Γ => Real.sqrt (κ (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 x))) ∧
      ∑' γ : X.Γ, Real.sqrt (κ (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 x)) ≤ C₁.toReal := by
    intro x hx
    have hne : ∑' γ : X.Γ, ENNReal.ofReal (Real.sqrt (κ (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 x))) ≠ ⊤ :=
      ((hC₁b x hx).trans_lt hC₁).ne
    have hS := ENNReal.summable_toReal hne
    simp only [ENNReal.toReal_ofReal, Real.sqrt_nonneg] at hS
    refine ⟨hS, ?_⟩
    rw [← ENNReal.ofReal_le_iff_le_toReal hC₁.ne,
      ENNReal.ofReal_tsum_of_nonneg (fun _ => Real.sqrt_nonneg _) hS]
    exact hC₁b x hx
  have horth : ∀ x, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ∀ γ : X.Γ,
      ‖P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 x)‖ ≤ max C 0 * Real.sqrt (κ (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 x)) := by
    intro x hx γ
    have h := (hl _ (isOrth_lact_of_isOrth X γ.2 hx) 0 (by rwa [norm_zero])).2
    rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  have hlocal : ∀ x ∈ X.dom, ∃ t : Set (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), IsOpen t ∧ x ∈ t ∧ t ⊆ X.dom ∧
      ∃ u : X.Γ → ℝ, Summable u ∧
        ∀ γ : X.Γ, ∀ y ∈ t, ‖(X.χ la γ.1)⁻¹ * P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 y)‖ ≤ u γ := by
    intro x hx
    have hb : _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx
    have hx'o : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx
    have hx'd : _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) ∈ X.dom := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb
    have hc : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF X (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF_mem X hb
    have hxc : x = _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) 0)
        (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF X (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)) := by
      rw [_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.cpt_zero, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_assoc, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_invF X hb, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.rmul_oneF]
    obtain ⟨D⟩ := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.luData_of _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.lu_holds X _ hx'o
    have huniq := D.uniq 0 (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IW.zero_mem_OmF X _ hx'o) _ hc
    rw [← hxc] at huniq
    have hcell : x ∈ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.cell D := ⟨hx, huniq.1⟩
    have hmem : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.cell D ∈ 𝓝 x := (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.isOpen_cell D).mem_nhds hcell
    have hzc : ContinuousAt D.zOf x := (D.hz.differentiableAt hmem).continuousAt
    have hbc : ContinuousAt D.bOf x := (D.hb.differentiableAt hmem).continuousAt
    have hchar : ContinuousAt (fun y => _root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la (D.bOf y)) x := by
      have h := continuousAt_bchar_of_ne_zero X la (bchar_ne_zero_of_mem_bor_torus_haar_measure X la hc)
      rw [← huniq.2.2] at h
      exact h.comp hbc
    have h1 : ∀ᶠ y in 𝓝 x, ‖D.zOf y‖ < ρ := by
      filter_upwards [hzc.eventually (Metric.ball_mem_nhds (D.zOf x) hρ)] with y hy
      rwa [huniq.2.1, dist_zero_right] at hy
    have h2 : ∀ᶠ y in 𝓝 x,
        ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la (D.bOf y)‖ < ‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF X (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x))‖ + 1 := by
      filter_upwards [hchar.eventually (Metric.ball_mem_nhds _ one_pos)] with y hy
      rw [dist_eq_norm, huniq.2.2] at hy
      have := norm_sub_norm_le (_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la (D.bOf y)) (_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF X (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)))
      linarith
    obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 ((Filter.eventually_of_mem hmem fun y hy => hy).and (h1.and h2))
    refine ⟨t, hto, hxt, fun y hy => (ht y hy).1.1, fun γ =>
      (‖_root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf.invF X (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x))‖ + 1) *
        (max C 0 * Real.sqrt (κ (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x))))),
      ((hsq _ hx'd).1.mul_left _).mul_left _, ?_⟩
    intro γ y hy
    obtain ⟨⟨hyd, hyΔ⟩, hyz, hyb⟩ := ht y hy
    obtain ⟨-, hbB, hsplit⟩ := D.split y hyd hyΔ
    have hl' := hl _ (isOrth_lact_of_isOrth X γ.2 hx'o) (D.zOf y) hyz
    rw [cpt_lact_eq_lact_cpt] at hl'
    rw [norm_mul, norm_inv, norm_chi_eq_one_of_mem_gamma X la γ.2, inv_one, one_mul, hsplit,
      ← rmul_lact_comm, hP.2 _ hl'.1 _ hbB, norm_mul]
    exact mul_le_mul hyb.le (hl'.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.sqrt_nonneg _))) (norm_nonneg _) (by positivity)
  have hsumm : ∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 x)‖ := by
    intro x hx
    obtain ⟨t, -, hxt, -, u, hu, hbd⟩ := hlocal x hx
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun γ => hbd γ x hxt) hu
  have hdiff : DifferentiableOn ℂ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P) X.dom := by
    intro x hx
    obtain ⟨t, hto, hxt, htd, u, hu, hbd⟩ := hlocal x hx
    have h := hWeier (_root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) X.Γ t (fun γ y => (X.χ la γ.1)⁻¹ * P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 y)) u hto
      (fun γ => ((hP.1.comp (differentiable_lact' X γ.1).differentiableOn
        (fun y hy => _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_lact X γ.2 (htd hy))).const_mul _)) hu hbd
    exact ((h x hxt).differentiableAt (hto.mem_nhds hxt)).differentiableWithinAt
  have hrmul : ∀ x ∈ X.dom, ∀ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r,
      _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) = _root_.ReciprocityTheory.ChartRestriction.G.FD.bchar la b * _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P x := by
    intro x hx b hb
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.poin
    rw [← tsum_mul_left]
    refine tsum_congr fun γ => ?_
    rw [← rmul_lact_comm, hP.2 _ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_lact X γ.2 hx) b hb]
    ring
  have hlact : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom,
      _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) = X.χ la γ * _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P x := by
    intro γ0 hγ0 x hx
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.poin
    rw [← tsum_mul_left]
    conv_rhs => rw [← (Equiv.mulRight (⟨γ0, hγ0⟩ : X.Γ)).tsum_eq]
    refine tsum_congr fun γ => ?_
    simp only [Equiv.coe_mulRight, Subgroup.coe_mul, Subgroup.coe_mk]
    rw [lact_lact_eq_lact_mul', X.χ_mul la γ γ.2 γ0 hγ0, mul_inv]
    have h0 := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IC.chi_ne_zero X la hγ0
    calc _ = X.χ la γ0 * (X.χ la γ0)⁻¹ *
          ((X.χ la γ)⁻¹ * P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact ((γ : GL (Fin r) E) * γ0) x)) := by
          rw [mul_inv_cancel₀ h0, one_mul]
      _ = _ := by ring
  have hsec : X.IsSec la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P) := ⟨hdiff, hrmul, hlact⟩
  refine ⟨hsumm, hsec, max C 0 * C₁.toReal, fun x hx => ?_⟩
  have hb := _root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem X hx
  have hinv := hPnorm r X la (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P) hsec 1 X.Γ.one_mem x hx _ hb
  rw [lact_one_apply] at hinv
  rw [← hinv, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IC.pnorm_orth X la _ (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx)]
  have hx'd : _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x) ∈ X.dom := _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb
  obtain ⟨hS, hSle⟩ := hsq _ hx'd
  have hle : ∀ γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)))‖ ≤
      max C 0 * Real.sqrt (κ (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)))) := by
    intro γ
    rw [norm_mul, norm_inv, norm_chi_eq_one_of_mem_gamma X la γ.2, inv_one, one_mul]
    exact horth _ (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf X hx) γ
  calc ‖_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x))‖
      ≤ ∑' γ : X.Γ, ‖(X.χ la γ.1)⁻¹ * P (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)))‖ :=
        norm_tsum_le_tsum_norm (hsumm _ hx'd)
    _ ≤ ∑' γ : X.Γ, max C 0 * Real.sqrt (κ (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)))) :=
        Summable.tsum_le_tsum hle (hsumm _ hx'd) (hS.mul_left _)
    _ = max C 0 * ∑' γ : X.Γ, Real.sqrt (κ (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x (_root_.ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf X x)))) :=
        tsum_mul_left
    _ ≤ max C 0 * C₁.toReal := mul_le_mul_of_nonneg_left hSle (le_max_right _ _)

end GlobalTheory.PoinHol
