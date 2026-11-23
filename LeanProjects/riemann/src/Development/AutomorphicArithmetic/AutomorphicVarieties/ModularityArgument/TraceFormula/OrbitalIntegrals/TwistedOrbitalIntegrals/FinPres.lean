import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubini

noncomputable section

open MeasureTheory Topology

namespace UpperTheory.V.Z.Tf.Orb

theorem finPres : FinPres := by
  intro G _ _ _ _ _ _ _ _ μ hμ θ hθ l hl hθl
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
  have hpow : ∀ j : ℕ, Continuous (θ ^ j : Monoid.End G) := by
    intro j
    induction j with
    | zero => exact continuous_id
    | succ j ih =>
      rw [pow_succ]
      exact ih.comp hθ
  have h1 : ∀ x, (θ ^ m : Monoid.End G) (θ x) = x := fun x => by
    have : (θ ^ (m + 1) : Monoid.End G) x = x := by rw [hθl]; rfl
    rw [pow_succ] at this
    exact this
  have h2 : ∀ x, θ ((θ ^ m : Monoid.End G) x) = x := fun x => by
    have : (θ ^ (m + 1) : Monoid.End G) x = x := by rw [hθl]; rfl
    rw [pow_succ'] at this
    exact this
  let e : G ≃* G :=
    { toFun := θ, invFun := (θ ^ m : Monoid.End G), left_inv := h1, right_inv := h2,
      map_mul' := map_mul θ }
  have hν : (Measure.map θ μ).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e hθ (hpow m)
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map θ μ = c • μ :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul (Measure.map θ μ) μ⟩
  have hj : ∀ j : ℕ, Measure.map (θ ^ j : Monoid.End G) μ = c ^ j • μ := by
    intro j
    induction j with
    | zero =>
      rw [pow_zero, pow_zero, one_smul]
      exact Measure.map_id
    | succ j ih =>
      have hcomp : ((θ ^ (j + 1) : Monoid.End G) : G → G) = (θ ^ j : Monoid.End G) ∘ θ := by
        rw [pow_succ]; rfl
      rw [hcomp, ← Measure.map_map (hpow j).measurable hθ.measurable, hc, Measure.map_smul, ih,
        smul_smul, pow_succ']
  have hfin : c ^ (m + 1) • μ = μ := by
    rw [← hj, hθl]
    exact Measure.map_id
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have hK0 : μ K ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ K.interior_nonempty).ne'
  have hKt : μ K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have hc1 : c ^ (m + 1) = 1 := by
    have h := congrArg (fun ν : Measure G => ν K) hfin
    simp only [Measure.coe_nnreal_smul_apply] at h
    have h' : ((c ^ (m + 1) : NNReal) : ENNReal) * μ K = 1 * μ K := by rw [one_mul]; exact h
    exact_mod_cast (ENNReal.mul_left_inj hK0 hKt).mp h'
  have hc2 : c = 1 := (pow_eq_one_iff_of_nonneg (by positivity) (Nat.succ_ne_zero m)).mp hc1
  refine ⟨hθ.measurable, ?_⟩
  rw [hc, hc2, one_smul]

end UpperTheory.V.Z.Tf.Orb
