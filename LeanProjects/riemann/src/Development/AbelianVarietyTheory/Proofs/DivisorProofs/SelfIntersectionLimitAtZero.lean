import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

theorem continuous_evS_shift {D : D7} {Y : ShimX D.what₂.Tau} (A : SlopeTestRemainingChoices Y)
    (P : MvPolynomial (Option (D.what₂.Tau × Fin Y.N)) ℝ) (u : Wt Y) :
    Continuous (fun s : ℝ => evS Y P (A.sh u s) s) := by
  unfold evS
  refine (MvPolynomial.continuous_eval P).comp (continuous_pi fun o => ?_)
  cases o with
  | none => exact continuous_id
  | some x =>
    simp only [Option.elim, SlopeTestRemainingChoices.sh]
    fun_prop

theorem eventually_dominant_shift {D : D7} {Y : ShimX D.what₂.Tau} (A : SlopeTestRemainingChoices Y) (u : Wt Y) (hu : RegDom u) :
    ∀ᶠ s : ℝ in 𝓝 0, Dominant Y (A.sh u s) := by
  unfold Dominant
  refine eventually_all.2 fun τ => eventually_all.2 fun a => eventually_all.2 fun b => ?_
  rcases lt_or_ge a b with h | h
  · have h1 : Continuous fun s : ℝ => A.sh u s τ b := by
      simp only [SlopeTestRemainingChoices.sh]; fun_prop
    have h2 : Continuous fun s : ℝ => A.sh u s τ a := by
      simp only [SlopeTestRemainingChoices.sh]; fun_prop
    have h3 : A.sh u 0 τ b < A.sh u 0 τ a := by simpa [SlopeTestRemainingChoices.sh] using hu τ a b h
    exact (h1.continuousAt.eventually_lt h2.continuousAt h3).mono fun s hs _ => hs.le
  · exact Eventually.of_forall fun s hab => by rw [le_antisymm hab h]

theorem tendsto_arSelfC_of_agree : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (A : SlopeTestRemainingChoices Y), Agree A → ∀ B : ℝ, 2 ≤ B →
    ∀ u : Wt Y, IsRat Y u → RegDom u → ∀ c,
      Tendsto (fun s : ℚ => Y.arSelfC (Y.Mbar B u s) c) (𝓝[>] (0 : ℚ)) (𝓝 (evS Y (A.Ps B c) u 0)) := by
  intro D Y A hA B hB u hr hu c
  obtain ⟨s₀, hs₀, C, hC⟩ := hA (supAbs Y u)
  have hcast : Tendsto (fun s : ℚ => (s : ℝ)) (𝓝[>] (0 : ℚ)) (𝓝 0) := by
    have h := (Rat.continuous_coe_real.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℚ)))
    simpa using h
  have h0 : A.sh u 0 = u := by
    funext τ i
    simp [SlopeTestRemainingChoices.sh]
  have hP : Tendsto (fun s : ℚ => evS Y (A.Ps B c) (A.sh u s) s) (𝓝[>] (0 : ℚ)) (𝓝 (evS Y (A.Ps B c) u 0)) := by
    have h := ((continuous_evS_shift A (A.Ps B c) u).tendsto 0).comp hcast
    rw [h0] at h
    exact h
  have hE : Tendsto (fun s : ℚ => Y.arSelfC (Y.Mbar B u s) c - evS Y (A.Ps B c) (A.sh u s) s)
      (𝓝[>] (0 : ℚ)) (𝓝 0) := by
    have hb : Tendsto (fun s : ℚ => C * (s : ℝ)) (𝓝[>] (0 : ℚ)) (𝓝 0) := by
      simpa using hcast.const_mul C
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [hcast.eventually (eventually_dominant_shift A u hu),
      hcast.eventually (eventually_le_nhds hs₀), self_mem_nhdsWithin] with s h1 h2 h3
    rw [Real.norm_eq_abs]
    exact hC B hB u s hr le_rfl h3 h2 h1 c
  simpa using hE.add hP

end GlobalTheory.Mean4
