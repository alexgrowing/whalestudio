import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.CuspPairB
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosT
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.IntegrableOfBd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CuspRapidDecayGL.CuspRapidDecaySiegelGL
import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.LieInvariants.InvariantOfLieOneLEqZero

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Set
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal Pointwise

namespace DiscreteGroups.T1.G.CP

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def bump (R : ℝ) (s : ℝ) : ℂ := ((max 0 (min 1 (R + 1 - |s|)) : ℝ) : ℂ)

theorem continuous_bump (R : ℝ) : Continuous (bump R) :=
  Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs)))

theorem hasCompactSupport_bump (R : ℝ) : HasCompactSupport (bump R) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(R + 1)) (b := R + 1)) fun s hs => ?_
  have h : R + 1 < |s| := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with h | h
    · have := neg_abs_le s; linarith
    · have := le_abs_self s; linarith
  simp only [bump]
  rw [max_eq_left (min_le_of_right_le (by linarith)), Complex.ofReal_zero]

theorem norm_bump_eq_one {R s : ℝ} (hs : |s| ≤ R) : ‖bump R s‖ = 1 := by
  simp only [bump]
  rw [min_eq_left (by linarith), max_eq_right zero_le_one, Complex.ofReal_one, norm_one]

theorem cp_vol (hn : 1 ≤ n) (D : Dom E n 0) (R : ℝ) : D.ν {x | |ldet x| ≤ R} < ⊤ := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E n (muG D)
  obtain ⟨K, hK, hKs⟩ := tsum_shift_le (bump R) (continuous_bump R) (hasCompactSupport_bump R) _
    (lg_e_pos (E := E) hn)
  have hS : MeasurableSet {x : H E n 0 | |ldet x| ≤ R} := by
    haveI := borelSpace_H (E := E) (n := n)
    exact (isClosed_le (continuous_abs.comp continuous_ldet) continuous_const).measurableSet
  have h1 : D.ν {x | |ldet x| ≤ R} ≤ ∫⁻ x, ‖bump R (lg x.1)‖ₑ ^ (2 : ℝ) ∂D.ν := by
    rw [← lintegral_indicator_one hS]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ {x : H E n 0 | |ldet x| ≤ R}
    · rw [indicator_of_mem hx, Pi.one_apply, ← ofReal_norm_eq_enorm, norm_bump_eq_one (s := lg x.1) hx,
        ENNReal.ofReal_one, ENNReal.one_rpow]
    · rw [indicator_of_notMem hx]
      exact zero_le
  have h2 : ∫⁻ x, ‖bump R (lg x.1)‖ₑ ^ (2 : ℝ) ∂D.ν =
      ∫⁻ g in stdDom (ratGL E n).range, ‖bump R (lg g)‖ₑ ^ (2 : ℝ) ∂muG D :=
    lintegral_nu D (fun g => ‖bump R (lg g)‖ₑ ^ (2 : ℝ)) fun γ hγ g => by rw [lg_rat_mul γ hγ g]
  have h3 : ∫⁻ g in stdDom (ratGL E n).range, ‖bump R (lg g)‖ₑ ^ (2 : ℝ) ∂muG D =
      ∫⁻ q, ∑' m : ℤ, ‖bump R (lg q.out + m * lg (splitCentre E n 1))‖ₑ ^ (2 : ℝ)
        ∂quotMeasure (latticeGL E n) (muG D) := by
    have h := lintegral_unfold (muG D) hn (fun _ => 1) (by intro _ _ _; rfl) aemeasurable_const
      (fun s => ‖bump R s‖ₑ ^ (2 : ℝ)) ((continuous_bump R).measurable.enorm.pow_const _)
    simpa only [one_mul] using h
  calc D.ν {x | |ldet x| ≤ R} ≤ _ := h1
    _ = _ := h2
    _ = _ := h3
    _ ≤ ∫⁻ _q, K ∂quotMeasure (latticeGL E n) (muG D) := lintegral_mono fun q => hKs _
    _ < ⊤ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top hK.lt_top (measure_lt_top _ _)

theorem cp_pairG (hRD : GlobalTheory.Published.CuspRapidDecaySiegelGL) {ψ : Sm E n} (hψ : IsCuspForm ψ)
    (hZ : ∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g) {φ : Sm E n} (hφ : IsAutForm φ)
    {u : ℝ → ℂ} (hu : Continuous u) (hus : HasCompactSupport u) {Ω : Set (GA E n)} (hΩ : IsCompact Ω) :
    ∃ C : ℝ, ∀ x : H E n 0, ∀ y ∈ Ω, ∀ y' ∈ Ω, ‖ψ.1 (x.1 * y) * u (ldet x) * φ.1 (x.1 * y')‖ ≤ C := by
  obtain ⟨Cu, hCu⟩ := hu.bounded_above_of_compact_support hus
  obtain ⟨R0, hR0⟩ := bound_of_hasCompactSupport hus
  obtain ⟨BΩ, hBΩ⟩ := hΩ.exists_bound_of_continuousOn
    (DiscreteGroups.T1.G.continuous_logAbs_det (E := E) (n := n)).continuousOn
  have hΩ2 : IsCompact (Ω⁻¹ * Ω) := hΩ.inv.mul hΩ
  obtain ⟨C, hC⟩ := cp_core hRD ψ φ hψ hZ hφ hΩ2 (R0 + BΩ)
  refine ⟨max C 0 * max Cu 0, fun x y hy y' hy' => ?_⟩
  by_cases h0 : u (ldet x) = 0
  · rw [h0, mul_zero, zero_mul, norm_zero]
    exact mul_nonneg (le_max_right _ _) (le_max_right _ _)
  have hl : |logAbs x.1.val.det| ≤ R0 := hR0 _ h0
  have hdet : |logAbs (x.1 * y).val.det| ≤ R0 + BΩ := by
    rw [lAbs_mul]
    have h := hBΩ y hy
    rw [Real.norm_eq_abs] at h
    exact (abs_add_le_abs_add_abs _ _).trans (add_le_add hl h)
  have hyy : y⁻¹ * y' ∈ Ω⁻¹ * Ω := Set.mul_mem_mul (Set.inv_mem_inv.2 hy) hy'
  have h1 := hC (x.1 * y) hdet _ hyy
  rw [show x.1 * y * (y⁻¹ * y') = x.1 * y' by group] at h1
  rw [norm_mul, norm_mul, mul_right_comm]
  exact mul_le_mul (h1.trans (le_max_left _ _)) ((hCu _).trans (le_max_left _ _)) (norm_nonneg _)
    (le_max_right _ _)

theorem pairBd_holds : PairBd := by
  intro E _ _ _ n hn D ψ φ u Ω hψ hZ hφ hu hus hΩ
  obtain ⟨C, hC⟩ := cp_pairG PositivityTheory.S2.CuspBdd.cuspRapidDecaySiegelGL hψ hZ hφ hu hus hΩ
  exact ⟨C, hC, cp_supp D (cp_vol hn D) hus⟩

theorem orthAct_holds : OrthAct := orthAct_of PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL pairBd_holds

end DiscreteGroups.T1.G.CP

end
