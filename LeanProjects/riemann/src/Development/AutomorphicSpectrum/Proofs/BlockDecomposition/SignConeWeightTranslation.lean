import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.ChainSum

theorem sdot_measurable {m : ℕ} (e : Fin m → SignType) : Measurable (sdot e) := by
  unfold sdot
  exact Finset.measurable_fun_sum _ fun i _ => (measurable_pi_apply i).const_mul _

theorem sdot_add' {m : ℕ} (e : Fin m → SignType) (a b : Fin m → ℝ) :
    sdot e (a + b) = sdot e a + sdot e b := by
  simp [sdot, mul_add, Finset.sum_add_distrib]

theorem chainSum_rest : ∀ m : ℕ, (∀ y : (Fin m → SignType) → ℝ, Measurable (gam y)) ∧
    (∀ (y : (Fin m → SignType) → ℝ) a b, gam (fun e => y e + sdot e b) (a + b) = gam y a) ∧
    ∀ (y y' : (Fin m → SignType) → ℝ) e s t a, (∀ e', SLe e e' ∨ SLe e' e → y e' = y' e') →
      gam (Function.update y e s) a - gam (Function.update y e t) a =
        gam (Function.update y' e s) a - gam (Function.update y' e t) a := by
  intro m
  refine ⟨fun y => ?_, fun y a b => ?_, fun y y' e s t a h => ?_⟩
  · unfold gam gamOn
    refine Finset.measurable_fun_sum _ fun c _ => ?_
    refine Measurable.const_mul (Finset.measurable_fun_prod _ fun e _ => ?_) _
    exact Measurable.ite (measurableSet_lt measurable_const (sdot_measurable e))
      measurable_const measurable_const
  · unfold gam gamOn
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun e _ => ?_
    have hiff : (y e + sdot e b < sdot e (a + b)) ↔ y e < sdot e a := by
      rw [sdot_add']
      exact add_lt_add_iff_right _
    exact if_congr hiff rfl rfl
  · unfold gam gamOn
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hchain : IsChain SLe (↑c : Set (Fin m → SignType)) := by
      simp only [Finset.mem_filter] at hc
      exact hc.2.2.1
    by_cases hec : e ∈ c
    · have key : ∀ u : ℝ, (∏ e' ∈ c, if Function.update y e u e' < sdot e' a then (1 : ℝ) else 0) =
          ∏ e' ∈ c, if Function.update y' e u e' < sdot e' a then (1 : ℝ) else 0 := by
        intro u
        refine Finset.prod_congr rfl fun e' he' => ?_
        by_cases hne : e' = e
        · subst hne
          simp only [Function.update_self]
        · have hcmp : SLe e e' ∨ SLe e' e :=
            hchain (Finset.mem_coe.2 hec) (Finset.mem_coe.2 he') (Ne.symm hne)
          simp only [Function.update_of_ne hne, h e' hcmp]
      rw [key s, key t]
    · have key : ∀ (z : (Fin m → SignType) → ℝ) (u v : ℝ),
          (∏ e' ∈ c, if Function.update z e u e' < sdot e' a then (1 : ℝ) else 0) =
            ∏ e' ∈ c, if Function.update z e v e' < sdot e' a then (1 : ℝ) else 0 := by
        intro z u v
        refine Finset.prod_congr rfl fun e' he' => ?_
        have hne : e' ≠ e := fun hh => hec (hh ▸ he')
        simp only [Function.update_of_ne hne]
      rw [key y s t, key y' s t, sub_self, sub_self]

end GlobalTheory.CompanionTheory.ChainSum
