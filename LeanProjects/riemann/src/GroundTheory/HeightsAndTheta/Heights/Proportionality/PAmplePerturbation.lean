import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Proportionality.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Proportionality

theorem AmplePerturbation.continuous_line {V : Type} [AddCommGroup V] [Module ℝ V] {D : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin D => V) ℝ) (x y : Fin D → V) :
    Continuous fun ε : ℝ => I (fun i => x i + ε • y i) := by
  classical
  have h : ∀ ε : ℝ, I (fun i => x i + ε • y i) =
      ∑ s : Finset (Fin D), (∏ i, (if i ∈ s then ε else 1)) * I (s.piecewise y x) := by
    intro ε
    have e1 : (fun i => x i + ε • y i) = (fun i => ε • y i) + x := by
      ext i; simp [add_comm]
    rw [e1, I.map_add_univ]
    refine Finset.sum_congr rfl fun s _ => ?_
    have e2 : s.piecewise (fun i => ε • y i) x =
        fun i => (if i ∈ s then ε else 1) • s.piecewise y x i := by
      ext i; by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
    rw [e2, I.map_smul_univ, smul_eq_mul]
  have hf : (fun ε : ℝ => I (fun i => x i + ε • y i)) = fun ε : ℝ =>
      ∑ s : Finset (Fin D), (∏ i, (if i ∈ s then ε else 1)) * I (s.piecewise y x) := funext h
  rw [hf]
  refine continuous_finsetSum _ fun s _ => (continuous_finsetProd _ fun i _ => ?_).mul
    continuous_const
  by_cases hi : i ∈ s <;> simp [hi, continuous_id', continuous_const]

theorem AmplePerturbation.proof : AmplePerturbation.Statement := by
  classical
  intro V _ _ D I L hyp H b
  obtain ⟨hD, -, hpos⟩ := hyp
  set j : Fin D := ⟨0, hD⟩ with hj
  set c : V := (2 : ℝ) • H + b with hc
  set x : Fin D → V := Function.update (fun _ => L) j c with hx
  set y : Fin D → V := Function.update (fun _ => H) j 0 with hy
  have hupd : ∀ ε : ℝ, Function.update (fun _ => L + ε • H) j c = fun i => x i + ε • y i := by
    intro ε; ext i
    by_cases hi : i = j
    · subst hi; simp [hx, hy]
    · simp [hx, hy, Function.update_of_ne hi]
  have hG : ∀ ε : ℝ, I (Function.update (fun _ => L + ε • H) j (ε • c)) =
      ε * I (fun i => x i + ε • y i) := by
    intro ε
    rw [I.map_update_smul, smul_eq_mul, hupd]
  let φ : ℝ → ℝ := fun ε => I (fun i => L + ε • H) - (D : ℝ) * (ε * I (fun i => x i + ε • y i))
  have hφc : Continuous φ := by
    have h1 := AmplePerturbation.continuous_line I (fun _ => L) (fun _ => H)
    have h2 := AmplePerturbation.continuous_line I x y
    exact h1.sub (continuous_const.mul (continuous_id.mul h2))
  have hφ0 : 0 < φ 0 := by simp [φ, hpos]
  have hev : ∀ᶠ ε in nhds (0 : ℝ), 0 < φ ε :=
    (hφc.tendsto 0).eventually (lt_mem_nhds hφ0)
  obtain ⟨δ, hδ, hδφ⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  have hd : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεδ
  have := hδφ hd
  simp only [φ] at this
  rw [hG]
  linarith

end GroundTheory.Heights₂.Heights.Proportionality
