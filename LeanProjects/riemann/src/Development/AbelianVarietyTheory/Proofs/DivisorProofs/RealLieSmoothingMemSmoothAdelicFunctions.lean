import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemSpanK

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology Set
open scoped ContDiff

namespace GlobalTheory.AutGrowth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in

theorem contDiff_lmul_uncurry : ContDiff ℝ ∞ fun q : Lie E a × Lie E a => lmul q.1 q.2 := by
  have e : (fun q : Lie E a × Lie E a => lmul q.1 q.2) = fun q i j => ∑ k, q.1 i k * q.2 k j := by
    funext q i j
    rfl
  rw [e]
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ContDiff.sum fun k _ => ?_
  exact ((contDiff_apply ℝ _ k).comp ((contDiff_apply ℝ _ i).comp contDiff_fst)).mul
    ((contDiff_apply ℝ _ j).comp ((contDiff_apply ℝ _ k).comp contDiff_snd))

theorem contDiffOn_smoothing_integrand {α : Lie E a → ℂ} (hα : IsTest (invSet E a) α) {ψ : GA E a → ℂ}
    (hψ : ψ ∈ Sm E a) (g : GA E a) :
    ContDiffOn ℝ ∞ (fun q : Lie E a × Lie E a => α (-q.2) * chart ψ g (lmul q.1 (-q.2))) (invSet E a ×ˢ univ) := by
  rintro ⟨p, t⟩ ⟨hp, -⟩
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases ht : -t ∈ tsupport α
  · have hpt : lmul p (-t) ∈ invSet E a := IsUnit.mul hp (hα.2.2 ht)
    have h1 : ContDiffAt ℝ ∞ (fun q : Lie E a × Lie E a => lmul q.1 (-q.2)) (p, t) :=
      (contDiff_lmul_uncurry.comp (contDiff_fst.prodMk contDiff_snd.neg)).contDiffAt
    have h3 : ContDiffAt ℝ ∞ (fun q : Lie E a × Lie E a => chart ψ g (lmul q.1 (-q.2))) (p, t) :=
      by
        have h4 := contDiffAt_chart hψ g hpt
        exact h4.comp (p, t) h1
    exact (hα.1.comp contDiff_snd.neg).contDiffAt.mul h3
  · have h0 : α =ᶠ[𝓝 (-t)] 0 := notMem_tsupport_iff_eventuallyEq.1 ht
    have h2 : (fun q : Lie E a × Lie E a => α (-q.2)) =ᶠ[𝓝 (p, t)] fun _ => 0 :=
      ((continuous_snd.neg).continuousAt.tendsto (x := (p, t))).eventually h0
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [h2] with q hq
    simp [hq]

theorem smoothing_mem_Sm (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (ν : Measure (Lie E a)) [ν.IsAddHaarMeasure] (α : Lie E a → ℂ) (hα : IsTest (invSet E a) α)
    (ψ : GA E a → ℂ) (hψ : ψ ∈ Sm E a) : smoothing ν α ψ ∈ Sm E a := by
  intro g
  let G : Lie E a → Lie E a → ℂ := fun p t => α (-t) * chart ψ g (lmul p (-t))
  have hk : IsCompact ((fun t : Lie E a => -t) '' tsupport α) := hα.2.1.isCompact.image continuous_neg
  have hgs : ∀ p, ∀ x, p ∈ invSet E a → x ∉ (fun t : Lie E a => -t) '' tsupport α → G p x = 0 := by
    intro p x _ hx
    have : α (-x) = 0 := image_eq_zero_of_notMem_tsupport fun h => hx ⟨-x, h, neg_neg x⟩
    simp [G, this]
  have hf : LocallyIntegrable (fun _ : Lie E a => (1 : ℂ)) ν := locallyIntegrable_const 1
  have H := contDiffOn_convolution_right_with_param_comp (μ := ν) (n := ⊤) (ContinuousLinearMap.mul ℝ ℂ)
    (contDiffOn_const (c := (0 : Lie E a))) isOpen_invSet hk hgs hf (contDiffOn_smoothing_integrand hα hψ g)
  refine H.congr fun x hx => ?_
  obtain ⟨u, hu⟩ := hx
  obtain rfl : x = toL u.val := hu.symm
  rw [chart_val, smoothing, chart_mul, convolution_def]
  simp [G]

end GlobalTheory.AutGrowth
