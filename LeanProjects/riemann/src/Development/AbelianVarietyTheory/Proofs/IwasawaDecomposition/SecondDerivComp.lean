import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

noncomputable section

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal ContDiff Topology

namespace GlobalTheory.BetaInv

section General

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

def antiFn (F : W → ℂ) (u : W) (w : W) : ℂ := (fderiv ℝ F w u + Complex.I * fderiv ℝ F w (Complex.I • u)) / 2

def levi (F : W → ℂ) (x u : W) : ℂ :=
  (fderiv ℝ (antiFn F u) x u - Complex.I * fderiv ℝ (antiFn F u) x (Complex.I • u)) / 2

omit [CompleteSpace W] in
theorem levi_congr {F G : W → ℂ} {x : W} (h : F =ᶠ[𝓝 x] G) (u : W) : levi F x u = levi G x u := by
  have : antiFn F u =ᶠ[𝓝 x] antiFn G u := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with w hw
    simp only [antiFn, hw]
  simp only [levi, this.fderiv_eq]

omit [CompleteSpace W] in
theorem fderiv_antiFn {F : W → ℂ} {x : W} (h : ∀ b, DifferentiableAt ℝ (fun w => fderiv ℝ F w b) x) (u a : W) :
    fderiv ℝ (antiFn F u) x a = (fderiv ℝ (fun w => fderiv ℝ F w u) x a +
      Complex.I * fderiv ℝ (fun w => fderiv ℝ F w (Complex.I • u)) x a) / 2 := by
  have := (((h u).hasFDerivAt.add ((h (Complex.I • u)).hasFDerivAt.const_mul Complex.I)).mul_const (2⁻¹ : ℂ))
  have e : antiFn F u = fun w => (fderiv ℝ F w u + Complex.I * fderiv ℝ F w (Complex.I • u)) * 2⁻¹ := by
    funext w; simp only [antiFn, div_eq_mul_inv]
  rw [e]
  erw [this.fderiv]
  simp [div_eq_mul_inv, mul_comm, mul_add]

omit [CompleteSpace W] in
theorem second_deriv {F : W → ℂ} {y : W} (hF : ContDiffAt ℝ 2 F y) (b : W) :
    HasFDerivAt (fun w => fderiv ℝ F w b) ((fderiv ℝ (fderiv ℝ F) y).flip b) y := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ F) y :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have := h1.hasFDerivAt.clm_apply (hasFDerivAt_const b y)
  simpa using this

theorem second_deriv_comp {F : W → ℂ} {φ : W → W} {x : W} (hF : ContDiffAt ℝ 2 F (φ x)) (hφ : AnalyticAt ℂ φ x)
    (b : W) : DifferentiableAt ℝ (fun w => fderiv ℝ (F ∘ φ) w b) x ∧ ∀ a,
      fderiv ℝ (fun w => fderiv ℝ (F ∘ φ) w b) x a =
        fderiv ℝ (fderiv ℝ F) (φ x) (fderiv ℂ φ x a) (fderiv ℂ φ x b) +
          fderiv ℝ F (φ x) (fderiv ℂ (fderiv ℂ φ) x a b) := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ F) (φ x) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 : HasFDerivAt φ ((fderiv ℂ φ x).restrictScalars ℝ) x :=
    hφ.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have h3 : HasFDerivAt (fun w => fderiv ℂ φ w b) (((fderiv ℂ (fderiv ℂ φ) x).flip b).restrictScalars ℝ) x := by
    have := hφ.fderiv.differentiableAt.hasFDerivAt.clm_apply (hasFDerivAt_const b x)
    exact HasFDerivAt.restrictScalars ℝ (by simpa using this)
  have h4 := (h1.hasFDerivAt.comp x h2).clm_apply h3
  have e : (fun w => fderiv ℝ (F ∘ φ) w b) =ᶠ[𝓝 x] fun w => (fderiv ℝ F ∘ φ) w (fderiv ℂ φ w b) := by
    have hF' : ∀ᶠ y in 𝓝 (φ x), DifferentiableAt ℝ F y :=
      (hF.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)
    filter_upwards [hφ.continuousAt.eventually hF', hφ.eventually_analyticAt] with w hw1 hw2
    rw [(hw1.hasFDerivAt.comp w (hw2.differentiableAt.hasFDerivAt.restrictScalars ℝ)).fderiv]
    simp
  have h5 := h4.congr_of_eventuallyEq e
  refine ⟨h5.differentiableAt, fun a => ?_⟩
  rw [h5.fderiv]
  simp [add_comm]

theorem levi_comp {F : W → ℂ} {φ : W → W} {x : W} (hF : ContDiffAt ℝ 2 F (φ x)) (hφ : AnalyticAt ℂ φ x) (u : W) :
    levi (F ∘ φ) x u = levi F (φ x) (fderiv ℂ φ x u) := by
  have h1 := second_deriv_comp hF hφ
  have h2 := second_deriv hF
  simp only [levi, fderiv_antiFn fun b => (h1 b).1, fderiv_antiFn fun b => (h2 b).differentiableAt,
    fun b => (h1 b).2, fun b => (h2 b).fderiv, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_smul, Complex.I_mul_I, neg_smul, one_smul, map_neg]
  linear_combination (fderiv ℝ F (φ x) (fderiv ℂ (fderiv ℂ φ) x u u) / 4) * Complex.I_mul_I

end General

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem ddc_eq (f : Pt ι p q → ℝ) (z ξ : Pt ι p q) :
    ddc f z ξ = (levi (fun v => (f (unflat v) : ℂ)) (flat z) (flat ξ)).re / Real.pi := rfl

omit [Fintype ι] in
theorem unflat_flat' (z : Pt ι p q) : unflat (flat z) = z := rfl

omit [Fintype ι] in
theorem flat_mem {z : Pt ι p q} (hz : z ∈ DomI ι p q) : flat z ∈ DomFlat ι p q := hz

theorem ddc_inv {f : Pt ι p q → ℝ} (hf : SmoothOn fun z => (f z : ℂ)) {g : ι → GL (Fin p ⊕ Fin q) ℂ}
    (hg : g ∈ UpqI ι p q) (hinv : ∀ z ∈ DomI ι p q, f (moebI g z) = f z) {z : Pt ι p q} (hz : z ∈ DomI ι p q)
    (ξ : Pt ι p q) : ddc f (moebI g z) (fun τ => tanAct (g τ) (z τ) (ξ τ)) = ddc f z ξ := by
  obtain ⟨ho, H⟩ := GlobalTheory.HodgeDomain.ActionDeriv.isOpen_and_fderiv_moebI ι p q
  obtain ⟨hd, hD⟩ := H g hg
  have hz' : flat z ∈ DomFlat ι p q := hz
  have hw : flat (moebI g z) ∈ DomFlat ι p q := flat_mem fun τ => moeb_mem (hg τ (Set.mem_univ _)) (hz τ)
  have han := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn ho hd _ hz'
  have hF : ContDiffAt ℝ 2 (fun v => (f (unflat v) : ℂ)) (flat (moebI g z)) :=
    (hf.contDiffAt (ho.mem_nhds hw)).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have h2 : ((fun v => (f (unflat v) : ℂ)) ∘ fun v => flat (moebI g (unflat v))) =ᶠ[𝓝 (flat z)]
      fun v => (f (unflat v) : ℂ) := by
    filter_upwards [ho.mem_nhds hz'] with v hv
    rw [Function.comp_apply, unflat_flat', hinv _ hv]
  have h3 := hD z hz ξ
  have h4 : (fun v => flat (moebI g (unflat v))) (flat z) = flat (moebI g z) := by
    simp only [unflat_flat']
  rw [← h4] at hF
  have h5 := levi_comp (φ := fun v => flat (moebI g (unflat v))) (x := flat z) hF han (flat ξ)
  rw [h3, levi_congr h2] at h5
  simp only [unflat_flat'] at h5
  rw [ddc_eq, ddc_eq, h5]

theorem smoothOn_log_ri {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (B : BdData ι p q Γ) (i : Fin B.m) :
    SmoothOn fun w : Pt ι p q => (Real.log (B.ri i w) : ℂ) := by
  have h0 : ContDiffOn ℝ ∞ (fun v => B.nrm i (unflat v)) (DomFlat ι p q) :=
    Complex.reCLM.contDiff.comp_contDiffOn (B.nrm_smooth i)
  have h1 : ContDiffOn ℝ ∞ (fun v => B.ri i (unflat v)) (DomFlat ι p q) :=
    contDiffOn_const.sub ((h0.pow 2).log fun v hv => (pow_pos (B.nrm_pos i _ hv) 2).ne')
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn
    (h1.log fun v hv => ((Real.exp_pos 1).trans_le (B.exp_le_ri i hv)).ne')

theorem beta_inv : ∀ (ι : Type) [Fintype ι] (p q : ℕ) (Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)) (B : BdData ι p q Γ), Γ ≤ UpqI ι p q → ∀ γ ∈ Γ, ∀ z ∈ DomI ι p q, ∀ ξ : Pt ι p q, B.beta (moebI γ z) (fun τ => tanAct (γ τ) (z τ) (ξ τ)) = B.beta z ξ := by
  intro ι _ p q Γ B hΓ γ hγ z hz ξ
  rw [BdData.beta, BdData.beta, B.kae_inv γ hγ z hz]
  congr 2
  refine Finset.sum_congr rfl fun i _ => ddc_inv (smoothOn_log_ri B i) (hΓ hγ) (fun w hw => ?_) hz ξ
  simp only [BdData.ri, B.nrm_inv i γ hγ w hw]

end GlobalTheory.BetaInv
