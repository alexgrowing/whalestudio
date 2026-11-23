import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietySlabMeasure
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyProjectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionsGeneric
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotBotOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AffineOfCone
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNullSmaller
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

namespace VarietySlabMeasure

theorem isFiniteLinProj_of {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (h : ComplexSets.IsFiniteProjection J A) :
    IsFiniteLinProj J A :=
  ⟨h.injective, h.finite⟩

theorem fibreCount_le {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) {U : Matrix (Fin n) (Fin n) ℂ}
    {s : Fin d → Fin n} (hA : ComplexSets.IsFiniteProjection J (U.submatrix s id))
    (B : Set (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin d)) :
    {z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard ≤
      ComplexSets.projDegree J (U.submatrix s id) := by
  obtain ⟨-, hfin, hle⟩ := ComplexSets.FibreBound.proof n d J _ hJ hd hA (WithLp.ofLp x)
  calc _ ≤ (ComplexSets.fibre J (U.submatrix s id) (WithLp.ofLp x)).encard := by
        refine Set.encard_le_encard_of_injOn (f := fun z : EuclideanSpace ℂ (Fin n) => WithLp.ofLp z)
          ?_ (fun a _ b _ h => WithLp.ofLp_injective 2 h)
        rintro z ⟨⟨hz, -⟩, hx⟩
        exact ⟨hz, congrArg WithLp.ofLp hx⟩
    _ = ((ComplexSets.fibre J (U.submatrix s id) (WithLp.ofLp x)).ncard : ℕ∞) :=
        hfin.cast_ncard_eq.symm
    _ ≤ _ := by exact_mod_cast hle

end VarietySlabMeasure

theorem VarietySlabMeasure.proof (hG : ComplexSets.FiniteProjectionsGeneric.Statement)
    (hW : VarietyProjectionMass.Statement) (hP : IndefiniteRowSideFullHecke.ComplexSets.PolySublevel.Statement) :
    VarietySlabMeasure.Statement := by
  classical
  intro n d J u hJ hdim hu R
  rcases hdim.lt_or_eq with hlt | heq
  · refine ⟨1, 1, one_pos, one_pos, fun ε _ _ => ?_⟩
    calc _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J) := measure_mono fun z hz => hz.1
      _ = 0 := NullSmaller.proof n d J hlt
      _ ≤ _ := by simp
  obtain ⟨U, hU, hfin⟩ := (hG n d J hJ heq).2.2 1 (fun _ => 1)
  have hA : ∀ s : Fin d → Fin n, StrictMono s →
      ComplexSets.IsFiniteProjection J (U.submatrix s id) := fun s hs => by
    simpa using hfin 0 ⟨s, hs.injective⟩

  have hQ : ∀ s : Fin d → Fin n, ∃ Q : MvPolynomial (Fin d) ℂ, StrictMono s → Q ≠ 0 ∧
      ∀ z ∈ zeroSetEuc J, ‖z‖ ≤ R →
        ‖eval ((U.submatrix s id).mulVec fun j => z j) Q‖ ≤ ‖∑ j, u j * z j‖ := by
    intro s
    by_cases hs : StrictMono s
    · obtain ⟨Q, hQ0, hb⟩ := IndefiniteRowSideFullHecke.ComplexSets.SlabBound.affine n d J (U.submatrix s id) u hJ
        (VarietySlabMeasure.isFiniteLinProj_of (hA s hs)) hu
      obtain ⟨C, hC⟩ := hb R
      have hK : (0 : ℝ) < max C 1 := lt_max_of_lt_right one_pos
      refine ⟨MvPolynomial.C ((max C 1 : ℝ) : ℂ)⁻¹ * Q, fun _ => ⟨?_, fun z hz hzR => ?_⟩⟩
      · exact mul_ne_zero (by simpa using hK.ne') hQ0
      · rw [eval_mul, eval_C, norm_mul, norm_inv, Complex.norm_of_nonneg hK.le, inv_mul_le_iff₀ hK]
        exact (hC z hz hzR).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · exact ⟨0, fun h => absurd h hs⟩
  choose Q hQ using hQ

  have hR' : ∀ s : Fin d → Fin n, ∃ R' : ℝ, 0 < R' ∧
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ R → ‖rowsProj U s z‖ < R' := by
    intro s
    have hc : Continuous (rowsProj U s) := by
      unfold rowsProj
      fun_prop
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) R).exists_bound_of_continuousOn
      hc.continuousOn
    refine ⟨max K 0 + 1, by positivity, fun z hz => ?_⟩
    have := hK z (mem_closedBall_zero_iff.mpr hz)
    linarith [le_max_left K 0]
  choose R' hR'0 hR' using hR'

  have hS : ∀ s : Fin d → Fin n, ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ (StrictMono s → ∀ η : ℝ, 0 < η → η ≤ 1 →
      μH[((2 * d : ℕ) : ℝ)] {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 (R' s) ∧
        ‖eval (fun i => x i) (Q s)‖ ≤ η} ≤ ENNReal.ofReal (C * η ^ α)) := by
    intro s
    by_cases hs : StrictMono s
    · obtain ⟨C, α, hC, hα, hb⟩ := hP d (Q s) (hQ s hs).1 (R' s) (hR'0 s)
      exact ⟨C, α, hC, hα, fun _ => hb⟩
    · exact ⟨1, 1, one_pos, one_pos, fun h => absurd h hs⟩
  choose C α hC hα hS using hS
  set T := Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s) with hT

  obtain ⟨α₀, hα₀, hα₀le⟩ : ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ s ∈ T, α₀ ≤ α s := by
    by_cases hne : T.Nonempty
    · exact ⟨T.inf' hne α, (Finset.lt_inf'_iff hne).2 fun s _ => hα s,
        fun s hs => Finset.inf'_le _ hs⟩
    · exact ⟨1, one_pos, fun s hs => absurd ⟨s, hs⟩ hne⟩
  set N : (Fin d → Fin n) → ℕ := fun s => ComplexSets.projDegree J (U.submatrix s id)
  have hNC : 0 ≤ ∑ s ∈ T, (N s : ℝ) * C s :=
    Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (hC s).le
  refine ⟨∑ s ∈ T, (N s : ℝ) * C s + 1, α₀, by linarith, hα₀, fun ε hε hε1 => ?_⟩
  set B : Set (EuclideanSpace ℂ (Fin n)) := {z | ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε}
  have hB : MeasurableSet B := by
    have hc : Continuous fun z : EuclideanSpace ℂ (Fin n) => ‖∑ j, u j * z j‖ := by fun_prop
    exact (measurableSet_le continuous_norm.measurable measurable_const).inter
      (measurableSet_le hc.measurable measurable_const)
  have hεα : 0 < ε ^ α₀ := Real.rpow_pos_of_pos hε _
  have hterm : ∀ s ∈ T,
      (⨆ x : EuclideanSpace ℂ (Fin d),
          (({z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
          μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (zeroSetEuc J ∩ B)) ≤
        ENNReal.ofReal ((N s : ℝ) * C s * ε ^ α₀) := by
    intro s hs
    have hs' : StrictMono s := (Finset.mem_filter.mp hs).2
    rw [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    gcongr
    · refine iSup_le fun x => ?_
      have := VarietySlabMeasure.fibreCount_le hJ heq (hA s hs') B x
      exact_mod_cast ENat.toENNReal_le.mpr this
    · calc _ ≤ μH[((2 * d : ℕ) : ℝ)] {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 (R' s) ∧
            ‖eval (fun i => x i) (Q s)‖ ≤ ε} := by
            refine measure_mono ?_
            rintro _ ⟨z, ⟨hz, hzR, hzε⟩, rfl⟩
            exact ⟨mem_ball_zero_iff.mpr (hR' s z hzR), ((hQ s hs').2 z hz hzR).trans hzε⟩
        _ ≤ ENNReal.ofReal (C s * ε ^ α s) := hS s hs' ε hε hε1
        _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hε hε1 (hα₀le s hs)) (hC s).le)
  calc μH[((2 * d : ℕ) : ℝ)] {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε}
        = μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B) := rfl
    _ ≤ _ := hW n d J hJ heq U hU B hB
    _ ≤ ∑ s ∈ T, ENNReal.ofReal ((N s : ℝ) * C s * ε ^ α₀) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (∑ s ∈ T, (N s : ℝ) * C s * ε ^ α₀) :=
        (ENNReal.ofReal_sum_of_nonneg fun s _ => by have := hC s; positivity).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.sum_mul, add_mul, one_mul]
        linarith

end

end GroundTheory.Heights₂.Heights
