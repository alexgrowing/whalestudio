import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.RingOfCoveringDescent
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN

set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
namespace GlobalTheory.CovTop.RingStep
set_option maxHeartbeats 1000000 in
theorem ring_of_covering_descent_alt (_hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hG : _root_.GlobalTheory.CovTop.GramCondition) (hD : _root_.GlobalTheory.CovTop.DeepGoodness) : _root_.GlobalTheory.CovTop.RingCondition := by
  have hH := _root_.GlobalTheory.CovTop.Sizes.hostN_alt 4
  refine Closed.imp ((hG.and hD).and hH) fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C1, -, h1⟩, ⟨C2, -, h2⟩⟩, ⟨A, -, h3⟩⟩ := h
  refine ⟨0, le_rfl, ?_⟩
  obtain ⟨x0, hx⟩ := (h1.and h2).and h3
  refine ⟨x0, fun x hx' hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨⟨g1, g2⟩, g3⟩ := hx x hx' hle ι p hp
  have gram := g1 i
  have deep := g2 i hi Y hY
  have host := g3 i
  have hB := GlobalTheory.T.cuspFormLattice_slope_sq_goodCover_le_core _ p.T ((i : ℕ) + 1) Y _ _ (wtA (p.κ i)) (p.κ i).n (typeK p.fw p.F.lv2 i) p.fw.laws
    ⟨Nat.succ_pos _, i.2⟩ hY.1 (dom_wtA _) (fun f hf => hf.1) gram.2.2.2 deep.1
  have hrd := (log_rd_le_fieldSz Y.d.c₂.F).trans hY.1.size
  obtain ⟨⟨-, hL10, hLx, -⟩, -, -, -, -, -, -, -, -, hpp, ⟨hA1, hPPx, -⟩, hroom, -⟩ := host
  have hb : 391 * zBase (Fm.L x ι) ^ 2 ≤ (Fm.L x ι).sc.b := by
    have hm1 := (Fm.D x ι).R.two_le_m
    have hm2 := (Fm.D x ι).R.m_add_three_le_k
    have hf : (1 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast (by have := (Fm.D x ι).R.toFrame.ord_pos; show 1 ≤ 2 * (Fm.D x ι).R.toFrame.ord; omega : 1 ≤ (Fm.D x ι).R.f)
    have hr : (1 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast (by unfold Ranks.r; omega : 1 ≤ (Fm.D x ι).R.r)
    have hZ : 1 ≤ zBase (Fm.L x ι) := by
      unfold zBase
      have : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
      nlinarith
    have hX : (Fm.L x ι).sc.x ≤ (Fm.L x ι).sc.x ^ A := by
      calc (Fm.L x ι).sc.x = (Fm.L x ι).sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (Fm.L x ι).sc.x ^ A := Real.rpow_le_rpow_of_exponent_le (by linarith) hA1
    have hX4 : ((Fm.L x ι).sc.x ^ A) ^ (4 : ℝ) = ((Fm.L x ι).sc.x ^ A) ^ (4 : ℕ) := by
      exact_mod_cast Real.rpow_natCast ((Fm.L x ι).sc.x ^ A) 4
    have hZ2 : zBase (Fm.L x ι) ^ 2 ≤ zBase (Fm.L x ι) ^ 12 := pow_le_pow_right₀ hZ (by norm_num)
    have h1 : zBase (Fm.L x ι) ^ 2 ≤ (Fm.L x ι).sc.x ^ A := hZ2.trans (hpp.trans hPPx)
    generalize (Fm.L x ι).sc.x ^ A = X at *
    have hX10 : (10 : ℝ) ≤ X := (hL10.trans hLx).trans hX
    have h3 : (100 : ℝ) ≤ X * X := by nlinarith
    have h4 : (1000 : ℝ) ≤ X * X * X := by nlinarith
    have h2 : 391 * X ≤ X ^ 4 := by nlinarith
    rw [hX4] at hroom
    linarith
  show slope_sq _ (latDeep p i Y) - 2 * (Fm.L x ι).sc.b ≤ muCore p i
  have h2r : 2 * (Real.log |(discr Y.d.c₂.F : ℝ)| / Module.finrank ℚ Y.d.c₂.F) ≤ 2 * (Fm.L x ι).sc.b := by linarith
  exact le_trans (sub_le_sub_left h2r _) hB
end GlobalTheory.CovTop.RingStep
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covering_ring_of_prints_gram_deepGood : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.RingCondition := by
  first | exact @_root_.GlobalTheory.CovTop.RingStep.ring_of_covering_descent_alt | exact _root_.GlobalTheory.CovTop.RingStep.ring_of_covering_descent_alt | (intros; apply _root_.GlobalTheory.CovTop.RingStep.ring_of_covering_descent_alt <;> assumption)
end
end
