import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermAutomorphicFormIntegral

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump Metric Set
open scoped ContDiff

namespace GlobalTheory.WhitBump

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem contDiff_nu_apply (i k : Fin n) : ContDiff ℝ ∞ fun t : Vp E n => nu t i k := by
  by_cases h : i < k
  · have e : (fun t : Vp E n => nu t i k) = fun t => t ⟨(i, k), h⟩ := funext fun t => by simp [nu, h]
    rw [e]; exact contDiff_apply ℝ _ _
  · have e : (fun t : Vp E n => nu t i k) = fun _ => (if i = k then 1 else 0 : Cinf E) :=
      funext fun t => by simp [nu, h]
    rw [e]; exact contDiff_const

theorem contDiff_nu_mul : ContDiff ℝ ∞ fun q : Lie E n × Vp E n => toL (nu (-q.2) * Matrix.of q.1) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  show ContDiff ℝ ∞ fun q : Lie E n × Vp E n => ∑ k, nu (-q.2) i k * q.1 k j
  refine ContDiff.sum fun k _ => ?_
  exact ((contDiff_nu_apply i k).comp contDiff_snd.neg).mul
    ((contDiff_apply ℝ _ j).comp ((contDiff_apply ℝ _ k).comp contDiff_fst))

variable [IsTotallyComplex E]

theorem continuous_psiInf_sdM : Continuous fun t : Vp E n => psiInf (-sdM (nu t)) := by
  have hs : Continuous (sInf E) :=
    ((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))
  have hd : Continuous fun t : Vp E n => sdM (nu t) :=
    continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => (contDiff_nu_apply i j).continuous
  exact continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (hs.comp hd.neg))

theorem bumpInf_contDiffOn_invSet : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (f : Lie E n → ℝ),
    ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ invSet E n → ContDiffOn ℝ ∞ (bumpInf f) (invSet E n) := by
  intro E _ _ _ n f hf hcs hts
  intro x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_invSet x₀ hx₀
  set r := ε / 2 with hr
  have hr0 : 0 < r := by positivity
  have hB : closedBall x₀ r ⊆ invSet E n := (closedBall_subset_ball (by linarith)).trans hball

  let Φ : Lie E n × Lie E n → Vp E n := fun q p => (Matrix.of q.1 * Matrix.of (ConstTermSmooth.invM q.2)) p.1.1 p.1.2
  have hΦ : ContinuousOn Φ (tsupport f ×ˢ closedBall x₀ r) := by
    have hinv : ContinuousOn (fun q : Lie E n × Lie E n => ConstTermSmooth.invM q.2) (tsupport f ×ˢ closedBall x₀ r) :=
      ConstTermSmooth.contDiffOn_invM.continuousOn.comp continuous_snd.continuousOn fun q hq => hB hq.2
    refine continuousOn_pi.2 fun p => ?_
    show ContinuousOn (fun q : Lie E n × Lie E n => ∑ k, q.1 p.1.1 k * ConstTermSmooth.invM q.2 k p.1.2) _
    refine continuousOn_finset_sum _ fun k _ => ?_
    have h1 : Continuous fun q : Lie E n × Lie E n => q.1 p.1.1 k :=
      (continuous_apply k).comp ((continuous_apply p.1.1).comp continuous_fst)
    have h2 : ContinuousOn (fun q : Lie E n × Lie E n => ConstTermSmooth.invM q.2 k p.1.2) (tsupport f ×ˢ closedBall x₀ r) :=
      (((continuous_apply p.1.2).comp (continuous_apply k) : Continuous fun m : Lie E n => m k p.1.2)).comp_continuousOn hinv
    exact h1.continuousOn.mul h2
  set K := Φ '' (tsupport f ×ˢ closedBall x₀ r) with hK
  have hKc : IsCompact K := (hcs.isCompact.prod (isCompact_closedBall _ _)).image_of_continuousOn hΦ

  let g : Lie E n → Vp E n → ℂ := fun x y => (f (toL (nu (-y) * Matrix.of x)) : ℂ)
  have hgs : ∀ p, ∀ y, p ∈ ball x₀ r → y ∉ -K → g p y = 0 := by
    intro p y hp hy
    by_contra hne
    have h : f (toL (nu (-y) * Matrix.of p)) ≠ 0 := fun h => hne (by simp [g, h])
    refine hy (Set.mem_neg.2 ⟨(toL (nu (-y) * Matrix.of p), p), ⟨subset_tsupport _ h, ball_subset_closedBall hp⟩, ?_⟩)
    have hu : IsUnit (Matrix.of p).det := (Matrix.isUnit_iff_isUnit_det _).1 (hB (ball_subset_closedBall hp))
    funext q
    have e : Matrix.of (toL (nu (-y) * Matrix.of p)) * Matrix.of (ConstTermSmooth.invM p) = nu (-y) :=
      Matrix.mul_nonsing_inv_cancel_right _ _ hu
    show (Matrix.of (toL (nu (-y) * Matrix.of p)) * Matrix.of (ConstTermSmooth.invM p)) q.1.1 q.1.2 = _
    rw [e]
    simp [nu, q.2]
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (↿g) (ball x₀ r ×ˢ univ) :=
    (Complex.ofRealCLM.contDiff.comp (hf.comp contDiff_nu_mul)).contDiffOn
  have hF : LocallyIntegrable (fun t : Vp E n => psiInf (-sdM (nu t))) volume :=
    continuous_psiInf_sdM.locallyIntegrable
  have hv : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Lie E n => (0 : Vp E n)) (ball x₀ r) := contDiffOn_const
  have main := contDiffOn_convolution_right_with_param_comp (μ := volume)
    (ContinuousLinearMap.mul ℝ ℂ) hv isOpen_ball hKc.neg hgs hF hg
  have fin : ContDiffOn ℝ ∞ (bumpInf f) (ball x₀ r) := by
    refine main.congr fun x _ => ?_
    simp only [bumpInf, convolution_def, ContinuousLinearMap.mul_apply', zero_sub, neg_neg, g]
    exact integral_congr_ae (Filter.Eventually.of_forall fun t => mul_comm _ _)
  exact fin.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hr0))

end GlobalTheory.WhitBump
