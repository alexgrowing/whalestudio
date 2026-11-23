import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TendstoFinrankVeryAmple
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBigIffGenDeg
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiposTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartLatRank
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionLatticeFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiRankBounds.Development

namespace PositivityTheory.Pf1.MbRank

open MvPolynomial Filter Topology
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver chartRingOver)
open GlobalTheory.CompanionTheory.Hypotheses₂.NefVolume GroundTheory.Heights₂.Heights.ForSecondHalf

noncomputable section

theorem ShiftSectionsRankB.of_degreeGeneric (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    ShiftSectionsRankB.Statement := by
  intro K _ ι _ Ω _ y D A P0 hV hB hP0 hs q hq
  classical
  have := BigIffGenDeg.charZero_of_isArithVar hV
  have hy := BigIffGenDeg.coord_ne_zero_of_isArithVar hV
  set N := HermLine.zcomb A (fsH ι) (q : ℤ) 1 with hN
  have hR : ChartLatRank.Statement :=
    ChartLatRank.proof (SectionLatticeFinite.proof Closed.ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cond)
  have hrk : ∀ n : ℕ, (Module.finrank ℤ (chartLat y N.a n) : ℝ) = Module.finrank ℚ (chartLatQ y N.a n) :=
    fun n => by exact_mod_cast hR K ι Ω y N.a n hy
  obtain rfl | ⟨d, rfl⟩ : D = 0 ∨ ∃ d, D = d + 1 := by
    rcases D with _ | d
    · exact Or.inl rfl
    · exact Or.inr ⟨d, rfl⟩
  · have hconst : (fun n : ℕ => (Module.finrank ℤ (chartLat y N.a n) : ℝ) /
        ((n : ℝ) ^ 0 / ((Nat.factorial 0 : ℕ) : ℝ))) = fun _ => (genDeg (mCoordIdeal y) 0 N.a : ℝ) := by
      funext n
      rw [hrk n, ← SectionsDimZero.full K ι Ω y N.a n (by simpa using hV)]
      simp
    rw [hconst]
    exact tendsto_const_nhds
  · have hsN : IsSemipositiveRel P0 (mCoordIdeal y) N := by
      have h := SemiposTwist.proof K ι P0 (mCoordIdeal y) A 1 q hs
      simpa [hN] using h
    have hNef : NefOnGenericDeg (mCoordIdeal y) N.a :=
      nefOnGenericDeg_of_semipos NefOnGenericOfSemipos.proof hDG hP0 hsN
    set a := N.a with ha
    obtain ⟨hK, hS⟩ := (GlobalTheory.CompanionTheory.Relay.kleiman_input_nef_ample_section_count GlobalTheory.CompanionTheory.Relay.kleiman_genericPointSectionInput).2
    have : Nonempty K := hV.1
    have hI : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y = mIdealOver ℚ y := LiftBirationalNef.genIdeal_eq y
    have hP := isProjVarF_map_of_isArithVar hV
    have hnz := GlobalTheory.CompanionTheory.Ar.Relevant.exists_coord_ne_zero K ι Ω y (d + 1) hV
    have hdim : FieldNumbers.relDim (mIdealOver ℚ y) = ((d + 1 : ℕ) : WithBot (WithTop ℤ)) :=
      hI ▸ (FieldNumbers.CutRegular.relDim_eq_natCast_iff _ (d + 1)).2 hP.2
    have hnef : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.IsNef ℚ y a := fun W hW hle hW1 =>
      NefPlusAmpleDegree.nefOnF_of_nefOnGenericDeg hNef W
        ⟨(Bridge.isMultiProjPrime_iff W).mp hW, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
        (hI.le.trans hle)
    have hfinQ : ∀ b, FiniteDimensional ℚ (chartLatQ y b 1) := fun b =>
      GlobalTheory.CompanionTheory.GenericFibre.finiteDimensional_chartLatQ K ι Ω y (d + 1) b hV
    have hfd : ∀ b, FiniteDimensional ℚ (secOver ℚ y b) := fun b => by
      rw [← chartLatQ_eq_secOver]
      exact hfinQ b
    have hsh : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
        (Module.finrank ℚ (secOver ℚ y ((n : ℤ) • a + fun _ => (M : ℤ))) : ℝ) ≤
          (Module.finrank ℚ (secOver ℚ y ((n : ℤ) • a)) : ℝ) + C * (n : ℝ) ^ d := by
      intro M
      obtain ⟨C, hC⟩ := shiftSectionBound K ι Ω y (d + 1) a M (by omega) hV hB
      refine ⟨C, hC.mono fun n hn => ?_⟩
      have h := hn.2
      rw [Nat.add_sub_cancel, chartLatQ_eq_secOver, chartLatQ_eq_secOver] at h
      exact h
    have hlim := tendsto_finrank_nef hK hS hnz hdim hnef hfd hsh
    set F : ℝ := ((d + 1).factorial : ℝ) with hF
    have hfac : F ≠ 0 := by rw [hF]; exact_mod_cast (Nat.factorial_pos _).ne'
    have hgen : (genDeg (mCoordIdeal y) (d + 1) a : ℝ) =
        F * ((NumbersDVR.intNum ℚ (mIdealOver ℚ y) (fun _ : Fin (d + 1) => a) : ℝ) / F) := by
      rw [mul_div_cancel₀ _ hfac, ← hI]
      rfl
    rw [hgen]
    refine (hlim.const_mul F).congr' (Eventually.of_forall fun n => ?_)
    simp only
    rw [hrk n, ← chartLatQ_smul, chartLatQ_eq_secOver, div_div_eq_mul_div]
    ring

theorem ShiftSectionsRankUpper.of_degreeGeneric (hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) :
    ShiftSectionsRankUpper.Statement :=
  ShiftSectionsRankUpper.of_B (ShiftSectionsRankB.of_degreeGeneric hDG)

end

end PositivityTheory.Pf1.MbRank
