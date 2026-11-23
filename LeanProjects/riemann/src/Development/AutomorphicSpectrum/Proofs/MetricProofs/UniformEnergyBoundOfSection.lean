import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.UnifInt
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UIObjects
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TailDimZero
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

open GroundTheory.Heights₂.Heights.AnalyticLimit (TailLogBound tail tailLogBound_dim_zero)

theorem tailLogBound_of_phi_eq {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Yo : Set X) (r : X → ℝ) {Φ Ψ : Fin e → LocPot X} (h : ∀ i, (Φ i).φ = (Ψ i).φ) (CE : ℝ)
    (H : TailLogBound A Yo r Φ CE) : TailLogBound A Yo r Ψ CE := by
  have hD : locDens A Φ = locDens A Ψ := by
    funext j y
    simp only [locDens, h]
  intro R₀ hR
  obtain ⟨h1, h2⟩ := H R₀ hR
  refine ⟨?_, ?_⟩
  · unfold MIntegrable at h1 ⊢
    rw [← hD]
    exact h1
  · unfold mInt integralWith at h2 ⊢
    rw [← hD]
    exact h2

theorem tailLogBound_of_tailBound : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Θ : Fin e → LocPot X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X) (C₁ : ℝ), (∀ i, IsPotential A (Θ i)) → (∀ i, IsPosPot A (Θ i)) → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → 0 ≤ C₁ → ∃ CE : ℝ, 0 ≤ CE ∧ ∀ (u : Fin e → X → ℝ) (T : Fin e → LocPot X), (∀ i, A.Smooth (u i)) → (∀ i, IsPsh A (Θ i + LocPot.ofFun (u i))) → (∀ i, ∀ y ∉ bdry s, -C₁ * Real.log (rW L s y) ≤ u i y ∧ u i y ≤ 0) → (∀ i x y, (T i).φ x y = (Θ i).φ x y + u i y) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A (bdry s)ᶜ (rW L s) T CE := by
  intro tb e X _ _ _ A Θ L s n m W C₁ hΘ hΘp hL hS hsnc hle hC₁
  rcases Nat.eq_zero_or_pos e with rfl | he
  · obtain ⟨CE, hCE⟩ := tailLogBound_dim_zero A (bdry s)ᶜ (rW L s) (fun i => i.elim0)
    refine ⟨max CE 0, le_max_right _ _, fun u T _ _ _ _ R₀ hR₀ => ?_⟩
    have hTe : T = fun i => i.elim0 := funext fun i => i.elim0
    rw [hTe]
    obtain ⟨h1, h2⟩ := hCE R₀ hR₀
    refine ⟨h1, h2.trans ?_⟩
    have hpos : 0 < R₀ := lt_of_lt_of_le (Real.exp_pos 1) hR₀
    have hlog : 0 ≤ Real.log R₀ := by
      have h := Real.log_le_log (Real.exp_pos 1) hR₀
      rw [Real.log_exp] at h
      linarith
    have hk : 0 ≤ Real.log R₀ ^ (0 + 1) := by positivity
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hk) hpos.le
  · letI : MeasurableSpace X := borel X
    haveI : BorelSpace X := ⟨rfl⟩
    obtain ⟨C, hC⟩ := tb A Θ L s m W hΘ hΘp hL hS hsnc hle
    obtain ⟨hbm, hrm⟩ := TailBoundAlt.bdry_rW_meas A L s hL hS
    have hCp : 0 ≤ max C 0 * (C₁ + 3) :=
      mul_nonneg (le_max_right _ _) (by linarith)
    refine ⟨max C 0 * (C₁ + 3), hCp, fun u T hu hpsh hb hT => ?_⟩
    refine tailLogBound_of_phi_eq A _ _ (Φ := fun i => Θ i + LocPot.ofFun (u i))
      (fun i => funext fun x => funext fun y => (hT i x y).symm) _ ?_
    intro R₀ hR₀
    have hΦ : ∀ i, IsPotential A (Θ i + LocPot.ofFun (u i)) := fun i =>
      isPotentialAdd A _ _ (hΘ i) (isPotential_ofFun A _ (hu i))
    obtain ⟨hfin, hint⟩ := maMeasure_thm A (fun i => Θ i + LocPot.ofFun (u i)) hΦ hpsh
    have hpos : 0 < R₀ := lt_of_lt_of_le (Real.exp_pos 1) hR₀
    have hlog1 : 1 ≤ Real.log R₀ := by
      have h := Real.log_le_log (Real.exp_pos 1) hR₀
      rwa [Real.log_exp] at h
    have hSm : MeasurableSet (tail (bdry s)ᶜ (rW L s) R₀) :=
      hbm.compl.inter (measurableSet_le measurable_const hrm)
    have hgm : Measurable ((tail (bdry s)ᶜ (rW L s) R₀).indicator fun x => Real.log (rW L s x)) :=
      (Real.measurable_log.comp hrm).indicator hSm
    have hg0 : ∀ x, 0 ≤ (tail (bdry s)ᶜ (rW L s) R₀).indicator
        (fun x => Real.log (rW L s x)) x := by
      intro x
      refine Set.indicator_apply_nonneg fun hx => Real.log_nonneg ?_
      have h1 : (1 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      exact h1.trans (hR₀.trans hx.2)
    have hlin : ∫⁻ x, ENNReal.ofReal ((tail (bdry s)ᶜ (rW L s) R₀).indicator
          (fun x => Real.log (rW L s x)) x) ∂maMeasure A (fun i => Θ i + LocPot.ofFun (u i)) =
        ∫⁻ y in (bdry s)ᶜ ∩ {y | R₀ ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y))
          ∂maMeasure A (fun i => Θ i + LocPot.ofFun (u i)) := by
      have hfun : (fun x => ENNReal.ofReal ((tail (bdry s)ᶜ (rW L s) R₀).indicator
          (fun x => Real.log (rW L s x)) x)) = (tail (bdry s)ᶜ (rW L s) R₀).indicator
          (fun x => ENNReal.ofReal (Real.log (rW L s x))) := by
        funext x
        by_cases hx : x ∈ tail (bdry s)ᶜ (rW L s) R₀
        · simp only [Set.indicator_of_mem hx]
        · simp only [Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
      rw [hfun, lintegral_indicator hSm]
      rfl
    have hK : 0 ≤ max C 0 * (C₁ + 3) * Real.log R₀ ^ 2 / R₀ := by
      have : 0 ≤ Real.log R₀ ^ 2 := by positivity
      exact div_nonneg (mul_nonneg hCp this) hpos.le
    have hle1 : ∫⁻ x, ENNReal.ofReal ((tail (bdry s)ᶜ (rW L s) R₀).indicator
          (fun x => Real.log (rW L s x)) x) ∂maMeasure A (fun i => Θ i + LocPot.ofFun (u i)) ≤
        ENNReal.ofReal (max C 0 * (C₁ + 3) * Real.log R₀ ^ 2 / R₀) := by
      rw [hlin]
      refine (hC C₁ u hC₁ hu hpsh hb R₀ hR₀).2.trans (ENNReal.ofReal_le_ofReal ?_)
      have h2 : 0 ≤ Real.log R₀ ^ 2 := by positivity
      have h3 : (0 : ℝ) ≤ C₁ + 3 := by linarith
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) h3) h2) hpos.le
    have hI : Integrable ((tail (bdry s)ᶜ (rW L s) R₀).indicator fun x => Real.log (rW L s x))
        (maMeasure A (fun i => Θ i + LocPot.ofFun (u i))) :=
      ⟨hgm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall hg0)).2 (hle1.trans_lt ENNReal.ofReal_lt_top)⟩
    have hMI := ((hint _ hgm).1).2 hI
    refine ⟨hMI, ?_⟩
    rw [(hint _ hgm).2 hMI, integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall hg0) hgm.aestronglyMeasurable]
    refine (ENNReal.toReal_le_of_le_ofReal hK hle1).trans ?_
    have hpow : Real.log R₀ ^ 2 ≤ Real.log R₀ ^ (e + 1) :=
      pow_le_pow_right₀ hlog1 (by omega)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCp) hpos.le

end GlobalTheory.CompanionTheory.Ar.Giv
