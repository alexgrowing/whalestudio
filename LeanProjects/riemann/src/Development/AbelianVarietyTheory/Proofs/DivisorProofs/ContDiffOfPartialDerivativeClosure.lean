import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartials
open Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem contDiff_of_partials_in_smooth_span :
    ∀ (k : ℕ) (S : Set ((Fin k → ℝ) → ℂ)), (∀ f ∈ S, Continuous f) →
    (∀ f ∈ S, ∀ j : Fin k, ∃ (ι : Type) (_ : Fintype ι) (c : ι → (Fin k → ℝ) → ℂ) (g : ι → (Fin k → ℝ) → ℂ),
      (∀ i, ContDiff ℝ ∞ (c i)) ∧ (∀ i, g i ∈ S) ∧
      ∀ t, HasDerivAt (fun s : ℝ => f (t + s • Pi.single j 1)) (∑ i, c i t * g i t) 0) →
    ∀ f ∈ S, ContDiff ℝ ∞ f := by
  intro k S hcont hder
  have key : ∀ n : ℕ, ∀ f ∈ S, ContDiff ℝ n f := by
    intro n
    induction n with
    | zero =>
      intro f hf
      exact contDiff_zero.2 (hcont f hf)
    | succ n ih =>
      intro f hf
      have hD : ∀ j : Fin k, ∃ D : (Fin k → ℝ) → ℂ, ContDiff ℝ n D ∧
          ∀ t, HasDerivAt (fun s : ℝ => f (t + s • Pi.single j 1)) (D t) 0 := by
        intro j
        obtain ⟨ι, hι, c, g, hc, hg, hd⟩ := hder f hf j
        refine ⟨fun t => ∑ i, c i t * g i t, ContDiff.sum fun i _ => ?_, hd⟩
        exact ((hc i).of_le (mod_cast le_top)).mul (ih _ (hg i))
      choose D hDc hDd using hD
      have hF := GlobalTheory.hasFDerivAt_of_continuous_partials k f D (fun i t => by
          have h : HasDerivAt (fun s : ℝ => f (t + s • Pi.single i 1)) (D i t) (t i - t i) := by
            rw [sub_self]; exact hDd i t
          refine (h.comp_sub_const (t i) (t i)).congr_of_eventuallyEq
            (Eventually.of_forall fun s => ?_)
          show f (Function.update t i s) = f (t + (s - t i) • Pi.single i 1)
          congr 1
          ext m
          by_cases hm : m = i
          · subst hm; simp
          · simp [hm, Function.update_apply])
        (fun i => (hDc i).continuous)
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [hcast, contDiff_succ_iff_fderiv]
      refine ⟨fun t => (hF t).differentiableAt, by simp, ?_⟩
      have hfd : fderiv ℝ f = fun t => ∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D i t) :=
        funext fun t => (hF t).fderiv
      rw [hfd]
      exact ContDiff.sum fun i _ =>
        (ContinuousLinearMap.smulRightL ℝ (Fin k → ℝ) ℂ (ContinuousLinearMap.proj i)).contDiff.comp (hDc i)
  intro f hf
  exact contDiff_infty.2 fun n => key n f hf

end GlobalTheory
