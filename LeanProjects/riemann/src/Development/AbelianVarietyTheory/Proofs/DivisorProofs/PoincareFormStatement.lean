import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryNormZeroIffOpenComplStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScalarBoundsOfNormLeOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothInChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialSmoothOffDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormLogPotentialFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcBoundaryPotentialEqFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormBoundedByPositivePotentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradientBoundaryPotentialBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincarePotentialIsPotentialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareFormBoundOfDdcStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareFormTwoSidedBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalSectionSmoothPolydiscStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialComparableTsumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareMetricLocalBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPolydiscExistsAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialExtendsAcrossBoundaryStatement

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory

namespace GlobalTheory

theorem poincareForm_normalCrossings : PoincareFormStatement := by
  intro e X _ _ _ _ _ A K hK hKp m L s D hB
  obtain ⟨hzero, hopen⟩ := GlobalTheory.T.boundary_norm_zero_iff_open_compl A L s D hB
  have hnorm1 : ∀ i y, normSec (L i) (s i) y ≤ 1 := fun i y => (hB i).2.2.2 y
  have hne : ∀ y, y ∉ ⋃ i, D i → ∀ i, normSec (L i) (s i) y ≠ 0 := fun y hy i h =>
    hy (Set.mem_iUnion.2 ⟨i, (hzero i y).1 h⟩)
  have hSB := GlobalTheory.T.scalar_bounds_of_norm_le_one L s D hnorm1 hne
  have ha : ∀ ψ : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ → ∀ z ∈ ψ.target, ∀ w,
      0 ≤ formAt ψ K z w := by
    obtain ⟨C, hC, h⟩ := GlobalTheory.T.form_bounded_by_positive_potential A K K hK hK hKp
    intro ψ hψ z hz w
    have h1 := h ψ hψ z hz w
    have h2 := abs_nonneg (formAt ψ K z w)
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hCi : ∀ i : Fin m, ∃ C : ℝ, 0 < C ∧ ∀ ψ : OpenPartialHomeomorph X (Fin e → ℂ),
      IsCompatChart A ψ → ∀ z ∈ ψ.target, ∀ w, |formAt ψ (L i) z w| ≤ C * formAt ψ K z w :=
    fun i => GlobalTheory.T.form_bounded_by_positive_potential A (L i) K (hB i).1 hK hKp
  choose Cf hCf hCfb using hCi
  set Kc : ℝ := 1 + ∑ i, Cf i with hKcdef
  have hKc : 0 < Kc := by
    have : 0 ≤ ∑ i, Cf i := Finset.sum_nonneg fun i _ => (hCf i).le
    linarith
  have hchern : ∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsCompatChart A ψ →
      ∀ z ∈ ψ.target, ψ.symm z ∉ ⋃ j, D j → ∀ w,
      |ddcAt ψ (rComp L s i) z w| ≤ Kc * formAt ψ K z w := by
    intro i ψ hψ z hz hzD w
    have hzi : ψ.symm z ∉ D i := fun h => hzD (Set.mem_iUnion.2 ⟨i, h⟩)
    rw [GlobalTheory.T.ddc_boundary_potential_eq_form A L s D hB i ψ hψ z hz hzi w]
    have h1 := hCfb i ψ hψ z hz w
    have h0 := ha ψ hψ z hz w
    have hle : Cf i ≤ Kc := by
      have : Cf i ≤ ∑ j, Cf j :=
        Finset.single_le_sum (f := Cf) (fun j _ => (hCf j).le) (Finset.mem_univ i)
      linarith
    calc |formAt ψ (L i) z w| ≤ Cf i * formAt ψ K z w := h1
      _ ≤ Kc * formAt ψ K z w := mul_le_mul_of_nonneg_right hle h0
  obtain ⟨C7, hC7, h7⟩ := GlobalTheory.T.gradient_boundary_potential_bound A K L s D hK hKp hB
  have h7' : ∀ (i : Fin m) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)), IsCompatChart A ψ →
      ∀ z ∈ ψ.target, ψ.symm z ∉ ⋃ j, D j → ∀ w,
      gradSqAt ψ (rComp L s i) z w ≤ C7 * Real.exp (rComp L s i (ψ.symm z)) * formAt ψ K z w :=
    fun i ψ hψ z hz hzD w => h7 i ψ hψ z hz (fun h => hzD (Set.mem_iUnion.2 ⟨i, h⟩)) w
  have hTS : ∀ c : ℝ, 0 < c → c ≤ Real.exp 1 / (2 * (m + 1) * Kc) → TwoSided A K L s D c := by
    intro c hc hcs
    apply GlobalTheory.T.poincare_form_bound_of_ddc A K L s D Kc c hK hB hKc hchern ha hc
    have hm : (0 : ℝ) < 2 * (m + 1) * Kc := by positivity
    have h1 : c * (2 * (m + 1) * Kc) ≤ Real.exp 1 := by
      rwa [le_div_iff₀ hm] at hcs
    have h2 : 0 ≤ c * Kc := by positivity
    nlinarith [Real.exp_pos 1]
  refine ⟨Real.exp 1 / (2 * (m + 1) * Kc), by positivity, hopen, hSB, ?_, ?_⟩
  · intro c hc hcs
    have hT := hTS c hc hcs
    refine ⟨GlobalTheory.T.poincare_potential_is_potential A K L s D c hK hB, hT,
      GlobalTheory.T.poincare_form_two_sided_bound A K L s D Kc C7 c hK hB hopen hSB hKc hchern ha hC7 h7' hc hT, ?_⟩
    apply GlobalTheory.T.potential_extends_across_boundary A (poincarePot K L s c) D hopen (GlobalTheory.T.poincare_potential_is_potential A K L s D c hK hB)
      (GlobalTheory.T.adapted_polydisc_exists_at A L s D hB)
    intro ψ σ hψ
    obtain ⟨ρ, hρ, -, h⟩ := GlobalTheory.T.poincare_metric_local_bound A K L s D ψ σ hK hKp hB hψ
    exact ⟨ρ, hρ, h c hc hT⟩
  · intro ψ σ hψ
    obtain ⟨ρ, hρ, hρ2, hP2⟩ := GlobalTheory.T.poincare_metric_local_bound A K L s D ψ σ hK hKp hB hψ
    obtain ⟨C3, hC3, h3⟩ := GlobalTheory.T.boundary_potential_comparable_tsum A L s D ψ σ hB hψ
    refine ⟨ρ, hρ, hρ2, ⟨C3, hC3, fun z hz hzD => h3 z (Metric.ball_subset_ball hρ2 hz) hzD⟩,
      fun c hc hcs => hP2 c hc (hTS c hc hcs)⟩

end GlobalTheory
