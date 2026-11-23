import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtOneParameter

open Filter Topology

namespace GlobalTheory.OneParamMatrix

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem eq_exp_of_continuous_oneParameter {n : Type} [Fintype n] [DecidableEq n]
    (N : ℝ → Matrix n n ℂ) (hc : Continuous N) (h0 : N 0 = 1)
    (hm : ∀ s t, N (s + t) = N s * N t) :
    ∃ Y : Matrix n n ℂ, ∀ t : ℝ, N t = NormedSpace.exp (t • Y) := by
  have hd := GlobalTheory.LocWeil.DerComm.differentiableAt_oneParameter N hc h0 hm
  set Y := deriv N 0 with hY
  have hN : ∀ t, HasDerivAt N (N t * Y) t := by
    intro t
    have h1 : HasDerivAt (fun s => N t * N (s - t)) (N t * Y) t := by
      have h2 : HasDerivAt (fun s => N (s - t)) Y t := by
        have hd' : HasDerivAt N Y (t - t) := by rw [sub_self]; exact hd.hasDerivAt
        exact hd'.comp_sub_const t t
      exact h2.const_mul (N t)
    refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    simp only
    rw [← hm]; congr 1; ring
  refine ⟨Y, fun t => ?_⟩
  set f : ℝ → Matrix n n ℂ := fun s => N s * NormedSpace.exp ((-s) • Y) with hf
  have hfd : ∀ s, HasDerivAt f 0 s := by
    intro s
    have he : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-Y))) (NormedSpace.exp (s • (-Y)) * (-Y)) s :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) (-Y) s
    have he' : HasDerivAt (fun u : ℝ => NormedSpace.exp ((-u) • Y))
        (NormedSpace.exp ((-s) • Y) * (-Y)) s := by
      simpa [smul_neg, neg_smul] using he
    have := (hN s).mul he'
    refine this.congr_deriv ?_
    have hcomm : Y * NormedSpace.exp ((-s) • Y) = NormedSpace.exp ((-s) • Y) * Y :=
      ((Commute.refl Y).smul_right (-s)).exp_right.eq
    rw [mul_assoc, hcomm]
    simp [mul_neg]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hfd s).differentiableAt)
    (fun s => (hfd s).deriv) t 0
  have hf0 : f 0 = 1 := by simp [hf, h0]
  rw [hf0] at hconst
  have hinv : NormedSpace.exp ((-t) • Y) * NormedSpace.exp (t • Y) = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _)]
    simp
  calc N t = N t * (NormedSpace.exp ((-t) • Y) * NormedSpace.exp (t • Y)) := by rw [hinv, mul_one]
    _ = f t * NormedSpace.exp (t • Y) := by simp only [hf, mul_assoc]
    _ = NormedSpace.exp (t • Y) := by rw [hconst, one_mul]

end GlobalTheory.OneParamMatrix
