import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

namespace TailBoundAlt

theorem bdry_rW_meas {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (hL : IsPotential A L)
    (hs : IsSection A L s) : MeasurableSet (bdry s) ∧ Measurable (rW L s) := by
  classical
  obtain ⟨hrc, -⟩ := rW_open A L s hL hs
  have hbm : MeasurableSet (bdry s) := (LeviFormBoundaryTopology.isClosed_bdry hs).measurableSet
  refine ⟨hbm, ?_⟩
  have heq : rW L s = (bdry s)ᶜ.piecewise (rW L s) (fun _ => Real.exp 1) := by
    funext y
    by_cases hy : y ∈ bdry s
    · have hy' : s y y = 0 := hy
      simp [Set.piecewise, hy, rW, logNormSec, hy']
    · simp [Set.piecewise, hy]
  rw [heq]
  exact ContinuousOn.measurable_piecewise hrc continuousOn_const hbm.compl

theorem lintegral_rW_le {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (L : LocPot X)
    (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X) (hΦ : ∀ i, IsPotential A (Φ i))
    (hΦp : ∀ i, IsPsh A (Φ i)) (hL : IsPotential A L) (hs : IsSection A L s)
    (hsnc : IsSNC A L s m W) (hle : ∀ y, logNormSec L s y ≤ 0) :
    ∫⁻ y in (bdry s)ᶜ, ENNReal.ofReal (rW L s y) ∂maMeasure A Φ ≤
      ENNReal.ofReal (Real.exp 1 * mInt A Φ (fun _ => 1) - 2 * mInt A Φ (logNormSec L s)) := by
  obtain ⟨-, hrm⟩ := bdry_rW_meas A L s hL hs
  have hlm : Measurable (logNormSec L s) := by
    have : logNormSec L s = fun y => (Real.exp 1 - rW L s y) / 2 := by
      funext y; simp only [rW]; ring
    rw [this]
    exact (measurable_const.sub hrm).div_const 2
  obtain ⟨hfin, hint⟩ := maMeasure_thm A Φ hΦ hΦp
  have hlI := logNormIntegrable A L s m W hL hs hsnc Φ hΦ
  have hI : Integrable (logNormSec L s) (maMeasure A Φ) := ((hint _ hlm).1).1 hlI
  have h1 := (hint (fun _ => (1 : ℝ)) measurable_const).2
    (mIntegrableCont A Φ hΦ _ continuous_const)
  have h2 := (hint _ hlm).2 hlI
  have hrI : Integrable (rW L s) (maMeasure A Φ) := (integrable_const _).sub (hI.const_mul 2)
  have hr0 : 0 ≤ᵐ[maMeasure A Φ] rW L s := Filter.Eventually.of_forall fun y =>
    le_trans (Real.exp_pos 1).le (rW_ge L s hle y)
  calc ∫⁻ y in (bdry s)ᶜ, ENNReal.ofReal (rW L s y) ∂maMeasure A Φ
      ≤ ∫⁻ y, ENNReal.ofReal (rW L s y) ∂maMeasure A Φ := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal (∫ y, rW L s y ∂maMeasure A Φ) :=
        (ofReal_integral_eq_lintegral_ofReal hrI hr0).symm
    _ = _ := by
        congr 1
        rw [h1, h2]
        have : ∫ y, rW L s y ∂maMeasure A Φ =
            ∫ y, (Real.exp 1 - 2 * logNormSec L s y) ∂maMeasure A Φ := rfl
        rw [this, integral_sub (integrable_const _) (hI.const_mul 2), integral_const_mul,
          integral_const, integral_const, smul_eq_mul, smul_eq_mul]
        ring

theorem cons_pot {e : ℕ} {X : Type} [TopologicalSpace X] (_A : FinHolAtlas (e + 1) X)
    (p : LocPot X → Prop) (Q : LocPot X) (Φ : Fin e → LocPot X) (hQ : p Q) (hΦ : ∀ i, p (Φ i)) :
    ∀ i, p ((Fin.cons Q Φ : Fin (e + 1) → LocPot X) i) := by
  intro i
  induction i using Fin.cases with
  | zero => simpa using hQ
  | succ i => simpa using hΦ i

end TailBoundAlt

end

end ReciprocityTheory.AnForm.P
