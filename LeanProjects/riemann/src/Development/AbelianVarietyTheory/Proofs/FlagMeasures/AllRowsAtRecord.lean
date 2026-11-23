import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.LocalToGlobal.HilbertRowConditions.AllJoin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Formalism.LocalToGlobal.ThresholdSelection
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCountE
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsLab
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsPCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsCountBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsGoodRed
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JCountP
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.AllJoin Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

noncomputable section

namespace GlobalTheory.AllRowsAtRecord

open Formalism.L2.SG.AllRowsOf

def stdChar (D : D7) (k : Fin 2) : AddChar (ZMod (D.host.g k)) ℂ :=
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  ZMod.stdAddChar

theorem stdChar_ne (D : D7) (k : Fin 2) : stdChar D k ≠ 1 := by
  intro hk
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Fact (1 < D.host.g k) := ⟨(D.host.g_prime k).one_lt⟩
  change (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) = 1 at hk
  have h1 : (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) 1 = (ZMod.stdAddChar : AddChar (ZMod (D.host.g k)) ℂ) 0 := by
    rw [hk, AddChar.one_apply, AddChar.map_zero_eq_one]
  exact one_ne_zero (ZMod.injective_stdAddChar h1)

theorem countAllRows_of {D : D7} (A : AllRows D) {c c₃ : ℝ} (hc : 0 < c) (hcc : c ≤ c₃) (hN : 2 ≤ D.R.r)
    (hf : 1 ≤ D.R.f) (hC : Formalism.MainNotions.N.CylinderCountFamily.CountCylAt D A.toAt c₃) (hpos : 0 < DstarE A A.B.e) :
    CountAllRows A (epsC c D.R.r D.R.f) := by
  have hL : 0 < Real.log (D.R.r : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hN0 : (0 : ℝ) < D.R.r := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hN)
  have hf0 : (0 : ℝ) < D.R.f := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hf)
  have hP : 0 < (D.R.r : ℝ) * D.R.f * Real.log D.R.r := by positivity
  refine ⟨(Real.exp_pos _).le, ?_, hpos, fun k S => ?_⟩
  · unfold epsC
    have h0 : 0 < c * (D.R.r : ℝ) * D.R.f * Real.log D.R.r := by
      have := mul_pos hc hP
      linarith [this, show c * ((D.R.r : ℝ) * D.R.f * Real.log D.R.r) = c * (D.R.r : ℝ) * D.R.f * Real.log D.R.r by ring]
    have h1 := Real.exp_lt_exp.mpr (show -(c * (D.R.r : ℝ) * D.R.f * Real.log D.R.r) < 0 by linarith)
    rwa [Real.exp_zero] at h1
  · have h := hC k S
    change |((A.dimT (cyl D k S) : ℕ) : ℝ) - DstarE A (A.eT (cyl D k S))| ≤
      Real.exp (-c₃ * (A.B.I.n : ℝ) * (A.B.I.f : ℝ) * Real.log (A.B.I.n : ℝ)) * DstarE A (A.eT (cyl D k S)) at h
    rw [A.n_eq, A.f_eq] at h
    have hDs : 0 ≤ DstarE A (A.eT (cyl D k S)) :=
      (mul_nonneg_iff_of_pos_left (Real.exp_pos _)).mp (le_trans (abs_nonneg _) h)
    have hexp : Real.exp (-c₃ * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)) ≤ epsC c D.R.r D.R.f := by
      unfold epsC
      apply Real.exp_le_exp.mpr
      have e1 : -c₃ * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ) = -(c₃ * ((D.R.r : ℝ) * D.R.f * Real.log D.R.r)) := by ring
      have e2 : -(c * (D.R.r : ℝ) * (D.R.f : ℝ) * Real.log (D.R.r : ℝ)) = -(c * ((D.R.r : ℝ) * D.R.f * Real.log D.R.r)) := by ring
      rw [e1, e2]
      have := mul_le_mul_of_nonneg_right hcc hP.le
      linarith
    exact le_trans h (mul_le_mul_of_nonneg_right hexp hDs)

theorem allRows_at_record : Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (G : GoodOp X)
    (ι : D.s.HH ≃ₗᵢ[ℂ] HHX X) (n₀ : ℕ) (Alev C₃ c₃ cb c : ℝ), 0 < c → c ≤ c₃ → Formalism.L2.SG.ConcreteSettingExists.GapHyp D →
    AutTie D X.B X.pl → RowDictTie X G ι → GlobalTheory.LabPin.LabTie X ι → (∀ P, CountE.CountIdempotentsClass P D n₀ Alev C₃ c₃ cb) →
    AdmissibleBoundsFromSource.CountTheoremHypotheses D large₂ n₀ Alev C₃ cb → 4 * D.R.r < D.host.g 1 →
    ∃ A : AllRows D, LabelCountGoodInjective A ∧ AllJoinA A ∧ CountAllRows A (epsC c D.R.r D.R.f) := by
  intro hRF D large₂ X G ι n₀ Alev C₃ c₃ cb c hc hcc hG hAut hT hLab hCnt hp hg1
  have hL : RowsLab X := Formalism.L2.SG.Pf.AllRowsLab.rowsLab_holds X hRF hG G ι hT hLab hAut
  have hψ : ∀ k, stdChar D k ≠ 1 := stdChar_ne D
  have hB : CountBase X n₀ Alev C₃ cb := Formalism.L2.SG.Pf.AllRowsCountBase.countBase_of X hAut hp hg1
  refine ⟨Formalism.L2.SG.Pf.AllRowsClosed.allRowsOfL X (stdChar D) hψ hL, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact thirdTie_allRows (hI := etInt_holds X)
  · refine ⟨⟨X.pl, hAut⟩, fun v => Formalism.L2.SG.Pf.AllRowsCountBase.hc_X X hAut v, fun _ => ?_⟩
    change Formalism.MainNotions.S.SplitsCompl X.B.I.E X.B.g₀
    rw [X.g0_eq]
    exact Formalism.L2.SG.Pf.AllRowsCountBase.splits_X X 0
  · exact ⟨stdChar D, hψ, fun _ _ => rfl⟩
  · have hN : 2 ≤ D.R.r := le_trans (by norm_num) hG.1
    have hf : 1 ≤ D.R.f := by exact_mod_cast Formalism.MainNotions.S.one_le_f (D := D)
    have hTC := tieCountAt_allRowsOf (X := X) (ψ₀ := stdChar D) (hJ := ejIdem_holds D (stdChar D))
      (hU := etUniv_of X (redKer_of X (redKerOne_of X (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 0)
        (Formalism.L2.SG.Pf.AllRowsRedKer.redKerP_holds X 1))))
      (hO := Formalism.L2.SG.Pf.AllRowsClosed.etOne_holds X (stdChar D) hψ) (hI := etInt_holds X) (hL := hL) hB
      (fun _ _ => Formalism.L2.SG.Pf.AllRowsClosed.etAlg_holds X _)
      (fun k S => Formalism.L2.SG.Pf.AllRowsClosed.etUnip_holds X k S)
    have hC : Formalism.MainNotions.N.CylinderCountFamily.CountCylAt D (Formalism.L2.SG.Pf.AllRowsClosed.allRowsOfL X (stdChar D) hψ hL).toAt c₃ :=
      Formalism.MainNotions.N.CylinderCountFamily.countCylAt_of D _ (hCnt Formalism.MainNotions.S.CountE.PCount) hTC
        (Formalism.L2.SG.Pf.AllRowsPCount.pCountTie_holds X (stdChar D) hψ hL)
    obtain ⟨-, -, -, -, -, -, -, hpos⟩ := hB
    exact countAllRows_of _ hc hcc hN hf hC hpos

end GlobalTheory.AllRowsAtRecord
