import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem toC0_eq_of_coe (p : C₀(ℝ, ℂ)) (f : ℝ → ℂ) (h : ∀ y, p y = f y) : toC0 f = p := by
  have hf : f = ⇑p := funext fun y => (h y).symm
  subst hf
  have hc : Continuous (⇑p) ∧ Tendsto (⇑p) (cocompact ℝ) (𝓝 0) := ⟨p.continuous, p.zero_at_infty'⟩
  unfold toC0
  rw [dif_pos hc]
  ext y
  rfl

theorem exists_resolvent_C0 : ∃ r : C₀(ℝ, ℂ), ∀ y, r y = (((1 + y ^ 2)⁻¹ : ℝ) : ℂ) := by
  have hpos : ∀ y : ℝ, (1 + y ^ 2) ≠ 0 := fun y => by positivity
  have hcont : Continuous (fun y : ℝ => (((1 + y ^ 2)⁻¹ : ℝ) : ℂ)) := by
    refine Complex.continuous_ofReal.comp ?_
    exact (by fun_prop : Continuous fun y : ℝ => 1 + y ^ 2).inv₀ hpos
  have hat : Tendsto (fun y : ℝ => 1 + y ^ 2) (cocompact ℝ) atTop := by
    have h1 : Tendsto (fun y : ℝ => ‖y‖ ^ 2) (cocompact ℝ) atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp tendsto_norm_cocompact_atTop
    have h2 : Tendsto (fun y : ℝ => 1 + ‖y‖ ^ 2) (cocompact ℝ) atTop :=
      tendsto_atTop_add_const_left _ 1 h1
    simpa using h2
  have htend : Tendsto (fun y : ℝ => (((1 + y ^ 2)⁻¹ : ℝ) : ℂ)) (cocompact ℝ) (𝓝 0) := by
    have h3 : Tendsto (fun y : ℝ => (1 + y ^ 2)⁻¹) (cocompact ℝ) (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hat
    have h4 : Tendsto (fun y : ℝ => (((1 + y ^ 2)⁻¹ : ℝ) : ℂ)) (cocompact ℝ) (𝓝 ((0 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).comp h3
    rwa [Complex.ofReal_zero] at h4
  exact ⟨⟨⟨_, hcont⟩, htend⟩, fun y => rfl⟩

theorem phiRes_holds : PhiRes := by
  intro n _ _ μ _ E _ Ω T F c hS g T₀ hb N _
  obtain ⟨-, -, -, -, -, -, -, -, -, hPW, -⟩ := hS
  have h0 := (hPW c g T₀ hb).1 0
  simp only [pow_zero, one_mul] at h0
  obtain ⟨r, hr⟩ := exists_resolvent_C0
  have hT : F.Φ r = T := F.res r hr
  let q : C₀(ℝ, ℂ) := ⟨⟨hg c g, h0.1⟩, h0.2⟩
  have hq : ∀ y, q y = hg c g y := fun y => rfl
  have key : ∀ M : ℕ, ∃ p : C₀(ℝ, ℂ),
      (∀ y, p y = ((((1 + y ^ 2) ^ M)⁻¹ : ℝ) : ℂ) * hg c g y) ∧ F.Φ p = F.Φ q * T ^ M := by
    intro M
    induction M with
    | zero => exact ⟨q, fun y => by simp [hq], by simp⟩
    | succ M ih =>
      obtain ⟨p, hp, hΦ⟩ := ih
      refine ⟨p * r, fun y => ?_, ?_⟩
      · have : (p * r) y = p y * r y := rfl
        rw [this, hp, hr, pow_succ (1 + y ^ 2) M, mul_inv]
        push_cast
        ring
      · rw [F.map_mul, hΦ, hT, pow_succ, mul_assoc]
  obtain ⟨p, hp, hΦ⟩ := key N
  rw [toC0_eq_of_coe p _ hp, toC0_eq_of_coe q _ hq, hΦ]

end GlobalTheory.CompanionTheory.KerFc
