import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameSplit

theorem lintegral_le_of_section {A B : Type*} [NormedAddCommGroup A] [NormedAddCommGroup B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B]
    [ProperSpace A] [ProperSpace B]
    (μ : Measure A) [μ.IsAddHaarMeasure] (ν : Measure B) [ν.IsAddHaarMeasure]
    (L : A → B) (hL : Continuous L) (hadd : ∀ x y, L (x + y) = L x + L y)
    (s : B → A) (hs : ∀ b, L (s b) = b) (S : Set A) (hS : MeasurableSet S)
    (hinv : ∀ b x, s b + x ∈ S ↔ x ∈ S)
    (hb : ∀ C : ℝ, ∃ D : ℝ, ∀ x ∈ S, ‖L x‖ ≤ C → ‖x‖ ≤ D) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : B → ℝ≥0∞, Measurable g →
      ∫⁻ y in S, g (L y) ∂μ ≤ K * ∫⁻ z, g z ∂ν := by
  have hLm : Measurable L := hL.measurable
  set ρ : Measure B := (μ.restrict S).map L with hρ
  have happ : ∀ T : Set B, MeasurableSet T → ρ T = μ (L ⁻¹' T ∩ S) := by
    intro T hT
    rw [hρ, Measure.map_apply hLm hT, Measure.restrict_apply (hLm hT)]
  haveI : IsFiniteMeasureOnCompacts ρ := by
    refine ⟨fun T hT => ?_⟩
    obtain ⟨C, hC⟩ := hT.isBounded.exists_norm_le
    obtain ⟨D, hD⟩ := hb C
    rw [happ T hT.measurableSet]
    refine lt_of_le_of_lt (measure_mono (t := Metric.closedBall 0 D) ?_)
      (isCompact_closedBall (0 : A) D).measure_lt_top
    intro x hx
    simpa using hD x hx.2 (hC _ hx.1)
  haveI : ρ.IsAddLeftInvariant := by
    refine ⟨fun b => ?_⟩
    ext T hT
    have hm : Measurable fun z : B => b + z := (continuous_const.add continuous_id).measurable
    rw [Measure.map_apply hm hT, happ _ (hm hT), happ _ hT,
      ← measure_preimage_add μ (s b) (L ⁻¹' T ∩ S)]
    congr 1
    ext x
    simp [hadd, hs, hinv]
  refine ⟨(ρ.addHaarScalarFactor ν : ℝ≥0∞), ENNReal.coe_lt_top, fun g hg => le_of_eq ?_⟩
  rw [← lintegral_map hg hLm, ← hρ]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul ρ ν]
  rw [lintegral_smul_measure]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem frameSplit : (∀ (r : ℕ) (X : Data E r) (R : ℝ), ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ g : V (nd X) → ℝ≥0∞, Measurable g → ∫⁻ y in {y : Frame X.Ψ r | ∀ τ a c, ¬ c < a → ‖y τ a c‖ ≤ R}, g (WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1 ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2) ≤ K * ∫⁻ z, g z) := by
  intro r X R
  haveI h1 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := inferInstance
  haveI h2 : (volume : Measure (Fin r → Fin r → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  haveI h3 : (volume : Measure (Frame X.Ψ r)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  refine lintegral_le_of_section (volume : Measure (Frame X.Ψ r)) (volume : Measure (V (nd X)))
    (fun y => WithLp.toLp 2 fun j => y ((Fintype.equivFin (Ent X)).symm j).1
      ((Fintype.equivFin (Ent X)).symm j).2.1.1 ((Fintype.equivFin (Ent X)).symm j).2.1.2)
    ?_ ?_
    (fun z τ a c => if h : c < a then z ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩) else 0)
    ?_ _ ?_ ?_ ?_
  · refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => ?_)
    fun_prop
  · intro x y
    ext j
    simp
  · intro z
    ext j
    have h := ((Fintype.equivFin (Ent X)).symm j).2.2
    simp only [dif_pos h]
    exact congrArg (fun k => z k) ((Fintype.equivFin (Ent X)).apply_symm_apply j)
  · apply IsClosed.measurableSet
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun c =>
      isClosed_iInter fun _ => isClosed_le ?_ continuous_const
    fun_prop
  · intro z x
    simp only [Set.mem_setOf_eq, Pi.add_apply]
    refine forall_congr' fun τ => forall_congr' fun a => forall_congr' fun c =>
      forall_congr' fun h => ?_
    rw [dif_neg h, zero_add]
  · intro C
    refine ⟨max (max C R) 0, fun x hx hC => ?_⟩
    have h0 : 0 ≤ max (max C R) 0 := le_max_right _ _
    refine (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun a =>
      (pi_norm_le_iff_of_nonneg h0).2 fun c => ?_
    by_cases h : c < a
    · have := (PiLp.norm_apply_le _ ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, c), h⟩⟩)).trans hC
      have h' : ‖x τ a c‖ ≤ C := by
        have e := (Fintype.equivFin (Ent X)).symm_apply_apply ⟨τ, ⟨(a, c), h⟩⟩
        simp only at this
        erw [e] at this
        exact this
      exact h'.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (hx τ a c h).trans ((le_max_right _ _).trans (le_max_left _ _))

end GlobalTheory.FrameSplit
