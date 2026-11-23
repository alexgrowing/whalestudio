import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsPosDensMeasurable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsSemiPosMassFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsIntegrable
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem PtsPosDensIntegrable.proof (hMass : PtsSemiPosMassFinite.Statement) : PtsPosDensIntegrable.Statement := by
  intro K _ ι _ P e Ψ L g hP hΨ hL hg
  classical
  obtain ⟨M, hMb⟩ := PtsPosDens.exists_bound hg
  choose T hTs hTp hLTp using fun j => Inter.SemiPosTwist.proof Inter.TorusInvLevi.proof K ι (L j) (hL j)
  set N : Fin e → HermLine ι := fun j => ((L j).tensor (T j)).tensor (T j) with hNdef
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j =>
    ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (hL j) (hTs j)
  have hNs : ∀ j, IsSmoothHerm (N j) := fun j => ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor (hLT j) (hTs j)
  have hNp : ∀ j, Inter.IsSemiPosHerm (N j) := fun j =>
    PtsPosDens.isSemiPosHerm_tensor (hLT j) (hTs j) (hLTp j) (hTp j)
  have hfinM := hMass K ι P e Ψ N hP hΨ hNs hNp
  have hfib := fibreFinite K ι P e Ψ hP hΨ
  set C : ℝ := max M 0 * 3 ^ e with hCdef
  have hC : 0 ≤ C := by positivity

  have key : ∀ y w, max (sheetDensity P Ψ (pot L) g y w) 0 ≤
      C * max (sheetDensity P Ψ (pot N) (fun _ => 1) y w) 0 := by
    intro y w
    unfold sheetDensity
    by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
    · rw [dif_pos hγ, dif_pos hγ]
      have hS := hγ.choose_spec
      have hab : |maDensity (fun j y' => pot L j (hγ.choose y')) y| ≤
          3 ^ e * maDensity (fun j y' => pot N j (hγ.choose y')) y :=
        Inter.PointsAbsIntegrable.abs_maDensity_le hL hTs hTp hLTp hS
      have hmc : hγ.choose y ∈ mcPts P := hS.2.self_of_nhds.2.1
      have hgb : |g (hγ.choose y)| ≤ max M 0 := (hMb _ hmc.1).trans (le_max_left _ _)
      have hn : 0 ≤ maDensity (fun j y' => pot N j (hγ.choose y')) y :=
        nonneg_of_mul_nonneg_right ((abs_nonneg _).trans hab) (by positivity)
      calc max (g (hγ.choose y) * maDensity (fun j y' => pot L j (hγ.choose y')) y) 0
          ≤ |g (hγ.choose y) * maDensity (fun j y' => pot L j (hγ.choose y')) y| :=
            max_le (le_abs_self _) (abs_nonneg _)
        _ = |g (hγ.choose y)| * |maDensity (fun j y' => pot L j (hγ.choose y')) y| := abs_mul _ _
        _ ≤ max M 0 * (3 ^ e * maDensity (fun j y' => pot N j (hγ.choose y')) y) :=
            mul_le_mul hgb hab (abs_nonneg _) (le_max_right _ _)
        _ = C * max (1 * maDensity (fun j y' => pot N j (hγ.choose y')) y) 0 := by
            rw [one_mul, max_eq_left hn, hCdef]
            ring
    · rw [dif_neg hγ, dif_neg hγ, max_self, mul_zero]

  have hpt : ∀ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) g y) ≤
      ENNReal.ofReal C * ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) := by
    intro y
    rw [← ENNReal.ofReal_mul hC]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold ptsPosDens
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfib y), finsum_mem_eq_finite_toFinset_sum _ (hfib y),
      Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => key y w
  have hnn : ∀ y, 0 ≤ ptsPosDens P Ψ (pot L) g y := fun y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _
  refine ⟨PtsPosDens.aestronglyMeasurable hP hΨ hL hg, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)]
  calc ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot L) g y)
      ≤ ∫⁻ y, ENNReal.ofReal C * ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) := lintegral_mono hpt
    _ = ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ (pot N) (fun _ => 1) y) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfinM

end GroundTheory.Heights₂.Heights
