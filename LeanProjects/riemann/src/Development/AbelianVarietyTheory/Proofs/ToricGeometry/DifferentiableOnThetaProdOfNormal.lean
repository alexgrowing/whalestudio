import Mathlib
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open ReciprocityTheory.PTheta

namespace GlobalTheory

theorem differentiable_thetaTerm_prod {ι : Type} [Fintype ι] (a b : ι → ℝ) (l : ι → ℤ) :
    Differentiable ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => thetaTerm a b p.1 (Matrix.of p.2) l) := by
  unfold thetaTerm eC
  simp only [dotProduct, Matrix.mulVec, shiftVec, ofRealVec, Pi.add_apply, Matrix.of_apply]
  fun_prop

theorem differentiableOn_theta_prod_of_normal {ι : Type} [Fintype ι] (a b : ι → ℝ)
    {U : Set ((ι → ℂ) × (ι → ι → ℂ))} (hU : IsOpen U)
    (hle : ∀ K ⊆ U, IsCompact K → ∃ u : (ι → ℤ) → ℝ, Summable u ∧
      ∀ l, ∀ p ∈ K, ‖thetaTerm a b p.1 (Matrix.of p.2) l‖ ≤ u l) :
    DifferentiableOn ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => theta a b p.1 (Matrix.of p.2)) U := by
  intro c hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hc
  have hK : Metric.closedBall c (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨u, hu, hbd⟩ := hle _ hK (isCompact_closedBall c (ε / 2))
  have hr : (0 : ℝ) < ε / 4 := by positivity
  have hlim : TendstoUniformlyOn
      (fun s : Finset (ι → ℤ) => fun p : (ι → ℂ) × (ι → ι → ℂ) =>
        ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l)
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => theta a b p.1 (Matrix.of p.2)) Filter.atTop
      (Metric.ball c (2 * (ε / 4))) := by
    have h := tendstoUniformlyOn_tsum hu (fun l p hp => hbd l p hp)
    refine h.mono ?_
    intro p hp
    exact Metric.ball_subset_closedBall (by simpa [show 2 * (ε / 4) = ε / 2 by ring] using hp)
  have hF : ∀ᶠ s : Finset (ι → ℤ) in Filter.atTop, DifferentiableOn ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l)
      (Metric.ball c (2 * (ε / 4))) :=
    Filter.Eventually.of_forall fun s => by
      have h := Differentiable.sum (u := s) fun l _ => differentiable_thetaTerm_prod a b l
      have e : (fun p : (ι → ℂ) × (ι → ι → ℂ) => ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l) =
          ∑ l ∈ s, fun p : (ι → ℂ) × (ι → ι → ℂ) => thetaTerm a b p.1 (Matrix.of p.2) l := by
        funext p
        rw [Finset.sum_apply]
      rw [e]
      exact h.differentiableOn
  have hd := (GlobalTheory.SCV.tendstoUniformlyOn_fderiv_ball hlim hF).1
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

theorem thetaHolo_of_domainOpen_of_mTest (hopen : DomainOpenStatement)
    (hM : ThetaMTestStatement) : ThetaHoloStatement := by
  intro ι _ a b
  refine differentiableOn_theta_prod_of_normal a b ((hopen ι).preimage continuous_snd) ?_
  intro K hKU hK
  obtain ⟨u, hu, hbd⟩ := hM ι a K hK (fun p hp => hKU hp)
  exact ⟨u, hu, fun l p hp => hbd b p hp l⟩

end GlobalTheory
