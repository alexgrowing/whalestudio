import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOscillatorActionUnitaryPolynomialBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeakWeilRepEqUnitSmulOscillatorRealPointsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift.GenZero

theorem exists_hasDerivAt_char (s : ℝ → ℂ) (hs : ∀ t t', s (t + t') = s t * s t') (h0 : s 0 = 1)
    (hc : ContinuousAt s 0) : ∃ m : ℂ, HasDerivAt s m 0 := by
  have hcont : Continuous s := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    have e : s = fun t => s (t - t₀) * s t₀ := funext fun t => by rw [← hs, sub_add_cancel]
    rw [e]
    refine ContinuousAt.mul ?_ continuousAt_const
    exact ContinuousAt.comp (g := s) (f := fun t => t - t₀) (by simpa using hc) (by fun_prop)
  let g : ℝ → ℂ := fun x => ∫ y in (0 : ℝ)..x, s y
  have hg : ∀ x, HasDerivAt g (s x) x := fun x => (hcont.integral_hasStrictDerivAt 0 x).hasDerivAt
  obtain ⟨ε, hε⟩ : ∃ ε, g ε ≠ 0 := by
    by_contra hn
    push Not at hn
    have h1 : HasDerivAt g 0 0 := by
      rw [show g = fun _ => 0 from funext hn]
      exact hasDerivAt_const _ _
    have := (hg 0).unique h1
    rw [h0] at this
    exact one_ne_zero this
  have e : s = fun t => (g (t + ε) - g t) / g ε := by
    funext t
    rw [eq_div_iff hε]
    have h1 : g (t + ε) - g t = ∫ y in t..(t + ε), s y :=
      intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)
    rw [h1]
    have h2 := intervalIntegral.integral_comp_add_left (a := 0) (b := ε) s t
    rw [add_zero] at h2
    rw [← h2]
    simp only [hs, g]
    exact (intervalIntegral.integral_const_mul _ _).symm
  have h3 : HasDerivAt (fun t => g (t + ε)) (s (0 + ε)) 0 := HasDerivAt.comp_add_const 0 ε (hg _)
  exact ⟨_, ((h3.sub (hg 0)).div_const (g ε)).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => congrFun e t)⟩

theorem lie_of_path {ι : Type} [Fintype ι] [DecidableEq ι] (H X : Matrix ι ι ℂ) (m : ℝ → Matrix ι ι ℂ) (h0 : m 0 = 1)
    (hm : ∀ t, (m t)ᴴ * H * m t = H) (hX : ∀ k l, HasDerivAt (fun t => m t k l) (X k l) 0) :
    Xᴴ * H + H * X = 0 := by
  ext i j
  have h1 : HasDerivAt (fun t => ∑ l, (∑ k, star (m t k i) * H k l) * m t l j)
      (∑ l, ((∑ k, star (X k i) * H k l) * m 0 l j + (∑ k, star (m 0 k i) * H k l) * X l j)) 0 :=
    HasDerivAt.fun_sum fun l _ =>
      (HasDerivAt.fun_sum fun k _ => (hX k i).star.mul_const (H k l)).mul (hX l j)
  have e : (fun t => ∑ l, (∑ k, star (m t k i) * H k l) * m t l j) = fun _ => H i j := by
    funext t
    rw [← congrFun (congrFun (hm t) i) j]
    simp only [Matrix.mul_apply, conjTranspose_apply]
  rw [e] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  have h3 : (Xᴴ * H * m 0 + (m 0)ᴴ * H * X) i j = 0 := by
    rw [← h2]
    simp only [Matrix.add_apply, Matrix.mul_apply, conjTranspose_apply, Finset.sum_add_distrib]
  rwa [h0, conjTranspose_one, Matrix.mul_one, Matrix.one_mul] at h3

open scoped Classical

set_option maxHeartbeats 1000000 in
open GlobalTheory.RealWeil in

theorem exists_generator : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) → (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ, (∀ k l, HasDerivAt (fun t => GlobalTheory.RealWeil.mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ F : GlobalTheory.RealWeil.BB ψ S T, IsThetaFunO ψ S T F.1 → ∃ u : ℝ → GlobalTheory.RealWeil.BB ψ S T, (∀ t, ((u t).1 : WO S T → ℂ) = om (γ t) F.1) ∧ HasDerivAt u (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F + lam • F) 0 := by
  intro D θ σ h ψ hψ S T om hw hc γ hγ hadd hinf X hX
  have hγ0 : γ 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_left_cancel (a := γ 0) (by rw [← this, mul_one])
  have hH := isHeis_rhoB (S := S) (T := T) h hψ
  have hL := lie_of_path (HM S T) X (fun t => mM θ S T (γ t)) (by simp only [hγ0, map_one])
    (fun t => mM_unitary h.inf _) hX
  obtain ⟨κ, _, c, p, q, hq, hn⟩ := GlobalTheory.Mem.Lift.Normal.normal_quad (Ix S T) (HM S T) X HM_herm HM_det hL
  obtain ⟨Ω, hΩ, -, hd⟩ := GlobalTheory.T.hasDerivAt_oscillatorAction_unitaryPath_quadratic (Ix S T) (HM S T) HM_herm HM_det (BB ψ S T) (rhoV hψ σ S T) hH
    (GA D S × GA D T) (mM θ S T) (mM_unitary h.inf)
  obtain ⟨lam, hlam⟩ := hd γ X hγ0 hX κ c p q hq
  have sm := sm_of_theta (S := S) (T := T) h hψ
  choose s hs1 hs using fun t => GlobalTheory.T.weakWeilRep_eq_unit_smul_oscillator_real_points D θ σ h ψ hψ S T om hw Ω hΩ (γ t).1 (hinf t).1 (γ t).2 (hinf t).2
  replace hs : ∀ t (F : BB ψ S T), IsThetaFunO ψ S T F.1 → om (γ t) F.1 = s t • ((Ω (γ t) F).1 : WO S T → ℂ) := hs
  obtain ⟨-, hsmul, hsm, hone, hmul, -⟩ := hΩ
  have cs : ∀ (a : ℂ) (G : BB ψ S T), ((a • G).1 : WO S T → ℂ) = a • (G.1 : WO S T → ℂ) := fun _ _ => rfl
  have hne : ∀ t, s t ≠ 0 := fun t e => by simpa [e] using hs1 t
  have hD : ∀ F : BB ψ S T, IsThetaFunO ψ S T F.1 →
      HasDerivAt (fun t => Ω (γ t) F) (nOp (rhoV hψ σ S T) (HM S T) X F + lam • F) 0 := fun F hF =>
    hn _ _ hH F (sm F hF) ▸ hlam F (sm F hF)
  by_cases hex : ∃ F₀ : BB ψ S T, IsThetaFunO ψ S T F₀.1 ∧ F₀ ≠ 0
  swap
  · push Not at hex
    refine ⟨lam, fun F hF => ⟨fun t => Ω (γ t) F, fun t => ?_, hD F hF⟩⟩
    have e : Ω (γ t) F = 0 := by
      have := hsmul (γ t) 0 F (sm F hF)
      rw [zero_smul, zero_smul] at this
      exact (congrArg (Ω (γ t)) (hex F hF)).trans this
    rw [hs t F hF]
    beta_reduce
    rw [e]
    exact (smul_zero _).symm
  obtain ⟨F₀, hF₀, hne₀⟩ := hex
  have hΩne : ∀ g, Ω g F₀ ≠ 0 := by
    intro g e
    have h1 := hmul g⁻¹ g F₀ (sm _ hF₀)
    have h2 := hsmul g⁻¹ 0 F₀ (sm _ hF₀)
    rw [zero_smul, zero_smul] at h2
    rw [inv_mul_cancel, hone _ (sm _ hF₀), e, h2] at h1
    exact hne₀ h1
  have hth : ∀ t, IsThetaFunO ψ S T (Ω (γ t) F₀).1 := by
    intro t
    have h1 := (thetaSub ψ S T).smul_mem (s t)⁻¹ (hw.om_pres (γ t) _ hF₀)
    rw [hs t F₀ hF₀, smul_smul, inv_mul_cancel₀ (hne t), one_smul] at h1
    exact h1
  have hms : ∀ t t', s (t + t') = s t * s t' := by
    intro t t'
    have h1 := hs (t + t') F₀ hF₀
    rw [hadd, map_mul, Module.End.mul_apply, hs t' F₀ hF₀, map_smul, hs t _ (hth t'), ← hmul _ _ _ (sm _ hF₀),
      smul_smul] at h1
    have h2 : (s t' * s t) • Ω (γ t * γ t') F₀ = s (t + t') • Ω (γ t * γ t') F₀ := QB_ext fun x => by
      rw [cs, cs, h1]
    rw [← smul_left_injective ℂ (hΩne _) h2, mul_comm]
  have hs0 : s 0 = 1 := by
    have := hms 0 0
    rw [add_zero] at this
    exact mul_left_cancel₀ (hne 0) (by rw [← this, mul_one])
  obtain ⟨w, hw₀⟩ : ∃ w, (F₀.1 : WO S T → ℂ) w ≠ 0 := by
    by_contra hn'
    push Not at hn'
    exact hne₀ (QB_ext hn')
  have hcs : ContinuousAt s 0 := by
    have h1 : ContinuousAt (fun t => ev _ _ w (Ω (γ t) F₀)) 0 :=
      (ev _ _ w).continuous.continuousAt.comp (hD F₀ hF₀).continuousAt
    have h2 : ev _ _ w (Ω (γ 0) F₀) ≠ 0 := by
      rw [hγ0, hone _ (sm _ hF₀), ev_apply]
      exact hw₀
    have h3 : ContinuousAt (fun t => om (γ t) F₀.1 w) 0 := ((hc _ hF₀ w).comp hγ).continuousAt
    refine (h3.div h1 h2).congr ?_
    filter_upwards [h1.eventually_ne h2] with t ht
    rw [Pi.div_apply, div_eq_iff ht, hs t F₀ hF₀, ev_apply]
    rfl
  obtain ⟨m, hm⟩ := exists_hasDerivAt_char s hms hs0 hcs
  refine ⟨lam + m, fun F hF => ⟨fun t => s t • Ω (γ t) F, fun t => (cs _ _).trans (hs t F hF).symm, ?_⟩⟩
  have h1 := hm.smul (hD F hF)
  rw [hs0, one_smul, hγ0, hone _ (sm _ hF)] at h1
  rw [add_smul, ← add_assoc]
  exact h1

end GlobalTheory.Mem.Lift.GenZero

end
