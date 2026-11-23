import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRightMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit GlobalTheory.GJReg

noncomputable section
namespace GlobalTheory.GJReg

theorem differentiable_chiS {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) :
    Differentiable ℂ fun s : ℂ => chiS ν s g := by
  intro s
  unfold chiS apow
  have h0 : (((nabs k (gdet g) : ℝ)) : ℂ) ≠ 0 := by
    have : 0 < nabs k (gdet g) := NNReal.coe_pos.mpr distribHaarChar_pos
    exact_mod_cast this.ne'
  exact (differentiableAt_id.const_cpow (Or.inl h0)).const_mul _

theorem sum_chiS_eq_of_halfPlane : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (ν : kˣ →* ℂˣ) (m m' : ℕ) (c : Fin m → ℂ) (h : Fin m → GL (Fin n) k) (c' : Fin m' → ℂ)
    (h' : Fin m' → GL (Fin n) k) (s₀ : ℝ),
    (∀ s : ℂ, s₀ < s.re → ∑ i, c i * chiS ν s (h i) = ∑ i, c' i * chiS ν s (h' i)) →
    ∀ s : ℂ, ∑ i, c i * chiS ν s (h i) = ∑ i, c' i * chiS ν s (h' i) := by
  intro k _ _ _ _ n ν m m' c h c' h' s₀ hs s
  let F : ℂ → ℂ := fun s => ∑ i, c i * chiS ν s (h i) - ∑ i, c' i * chiS ν s (h' i)
  have hd : Differentiable ℂ F := by
    refine Differentiable.sub ?_ ?_
    · exact Differentiable.fun_sum fun i _ => (differentiable_chiS ν (h i)).const_mul (c i)
    · exact Differentiable.fun_sum fun i _ => (differentiable_chiS ν (h' i)).const_mul (c' i)
  have ha : AnalyticOnNhd ℂ F Set.univ := fun z _ => hd.analyticAt z
  have hev : F =ᶠ[nhds (((s₀ + 1 : ℝ)) : ℂ)] 0 := by
    have ho : IsOpen {t : ℂ | s₀ < t.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds (by simp)] with t ht
    simp only [F, Pi.zero_apply, hs t ht, sub_self]
  have := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ _) hev
    (Set.mem_univ s)
  exact sub_eq_zero.mp this

end GlobalTheory.GJReg
