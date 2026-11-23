import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.TargetSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartDenominator
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsLinearIndependentOfGenerates
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKodairaGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefSectionGrowth
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefShiftPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftSectionBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneQuotientBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHyperplaneSectionBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SiuZB.proof (hK : KodairaGeneric.Statement) (hZ : SectionsDimZero.Statement) : KH.SiuZStatement := by
  intro K _ ι _ Ω _ _ y D α I hI hV hB hNef hPos
  classical

  have hagree : ∀ (V : Ideal (MRingOver ℚ ι)) (n : ℕ) (L : Fin n → K → ℤ), IsProjVarF V n →
      I V n L = NumbersDVR.intNum ℚ V L := by
    obtain ⟨I₀, -, h₀⟩ := Targets.ExistsUnique.full ℚ ι
    intro V n L hVn
    rw [h₀ I hI V n L hVn, h₀ _ (NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) V n L hVn]
  have hG : IsProjVarF (KH.genIdeal y) D := isProjVarF_map_of_isArithVar hV
  have hdeg : 0 < genDeg (mCoordIdeal y) D α := by
    have h := hagree _ D (fun _ => α) hG
    rw [h] at hPos
    exact hPos

  obtain ⟨k, e, hk, he, hmem⟩ :
      ∃ (k : ℕ) (e : Ω), 1 ≤ k ∧ e ≠ 0 ∧ e ∈ chartLatQ y ((k : ℤ) • α - 1) 1 := by
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · have hr := hZ K ι Ω y ((1 : ℕ) • α - 1) 1 hV
      have hg : genDeg (mCoordIdeal y) 0 ((1 : ℕ) • α - 1) = genDeg (mCoordIdeal y) 0 α := by
        unfold genDeg
        congr 1
        funext j
        exact j.elim0
      rw [hg] at hr
      have hpos : 0 < Module.finrank ℚ (chartLatQ y ((1 : ℕ) • α - 1) 1) := by
        have : (0 : ℤ) < Module.finrank ℚ (chartLatQ y ((1 : ℕ) • α - 1) 1) := by rw [hr]; exact hdeg
        exact_mod_cast this
      have := Module.nontrivial_of_finrank_pos hpos
      obtain ⟨⟨e, he⟩, hne⟩ := exists_ne (0 : chartLatQ y ((1 : ℕ) • α - 1) 1)
      refine ⟨1, e, le_rfl, fun h => hne ?_, by simpa using he⟩
      exact Subtype.ext h
    · have hnef : NefOnGenericDeg (mCoordIdeal y) α := by
        intro W hW hPW
        have hWq : IsProjVarF (W.map (MvPolynomial.map (Int.castRingHom ℚ))) 1 :=
          isProjVarF_map_of_isArithVar (D := 1) hW
        have h := hNef _ hWq (Ideal.map_mono hPW)
        rw [hagree _ 1 _ hWq] at h
        unfold genDeg
        convert h using 2
        funext j
        fin_cases j
        rfl
      exact hK K ι Ω y D α hD hV hB hnef hdeg

  obtain ⟨n, hn, hns⟩ := ChartDenominator.proof K ι Ω y ((k : ℤ) • α - 1) 1 e hmem
  have hn0 : (n : Ω) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨k, hk, (n : Ω) * e, ?_, mul_ne_zero hn0 he⟩
  have hfun : (fun κ => (k : ℤ) * α κ - 1) = (k : ℤ) • α - 1 := by
    funext κ
    simp
  rw [hfun]
  exact hns

theorem SiuZB.of_kodaira (hK : KodairaGeneric.Statement) : KH.SiuZStatement :=
  SiuZB.proof hK SectionsDimZero.proof

end GroundTheory.Heights₂.Heights.ForSecondHalf
