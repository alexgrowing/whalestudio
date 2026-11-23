import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Formalism.LocalToGlobal.HilbertRowConditions.AllJoin
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Formalism.LocalToGlobal.ThresholdSelection
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.RowsDef
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCountE
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.GapClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountConstantsOfSiegelWeil
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountClausesClosed
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AllRowsAtRecord
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.GlobalTheoryTheory.ConcN Formalism.L2.GlobalTheoryTheory.AllJoin Formalism.L2.SG.HidaSetting Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PackageTie2

namespace GlobalTheory.IrrRowConcrete

theorem irr_row_closed : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → Formalism.L2.SG.RowsDef.RowsFinDim → ∃ cIc : ℝ, 0 < cIc ∧ ∀ 𝒞 : FamClass, (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → (Closed 𝒞 fun Fm _ => 𝒞 Fm → ∃ x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, ∃ (X : HidaSetting (Fm.D x i)) (G : GoodOp X) (ι : (Fm.D x i).s.HH ≃ₗᵢ[ℂ] HHX X), AutTie (Fm.D x i) X.B X.pl ∧ RowDictTie X G ι ∧ GlobalTheory.LabPin.LabTie X ι) → Closed 𝒞 fun Fm _ => ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ A : AllRows (Fm.D x i), LabelCountGoodInjective A ∧ AllJoinA A ∧ CountAllRows A (epsC cIc (Fm.D x i).R.r (Fm.D x i).R.f) := by
  intro hSW hRF
  obtain ⟨c30, cIc, hc30, hcI, hcle, hP⟩ := GlobalTheory.CountConstants.count_constants_of_siegelWeil hSW
  refine ⟨cIc, hcI, fun 𝒞 hT hX => ?_⟩
  have hcb : ∀ {eps : ℝ} (Fm : FamP eps), 0 < (c30 Fm.cOut).cb := fun Fm =>
    (hP (fun _ _ _ _ => True) Fm).2.1
  have hEv := GlobalTheory.IrrCountEv.countClauses_closed 𝒞 c30 hc30 hcb hT
  have hGap := Formalism.L2.SG.GapClosed.gapEv_closed_of 𝒞 hT
  obtain ⟨a1, ha1, H1⟩ := (hX.and hEv).and hGap
  refine ⟨a1, ha1, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := H1 e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  obtain ⟨⟨hx, hev⟩, hg⟩ := hK Fm CH hc hL
  obtain ⟨x1, hx1⟩ := hx hc
  obtain ⟨x2, hx2⟩ := hev
  obtain ⟨y, hy⟩ := hg hc
  refine ⟨max (max x1 x2) (max y (Fm.x1 + 1)), fun x hxge i => ?_⟩
  have hb : max (max x1 x2) (max y (Fm.x1 + 1)) ≤ x := hxge
  simp only [max_le_iff] at hb
  obtain ⟨⟨b1, b2⟩, b3, b4⟩ := hb
  obtain ⟨X, G, ι, hA, hR, hLab⟩ := hx1 x (by linarith) b1 i
  obtain ⟨hpar, h4⟩ := hx2 x b2 i
  exact GlobalTheory.AllRowsAtRecord.allRows_at_record hRF (Fm.D x i) (Fm.L x i) X G ι (c30 Fm.cOut).n0 (c30 Fm.cOut).A (c30 Fm.cOut).C
    (c30 Fm.cOut).c (c30 Fm.cOut).cb cIc hcI (hcle Fm) (hy x b3 i) hA hR hLab (fun P => (hP P Fm).2.2 x i) hpar h4

end GlobalTheory.IrrRowConcrete
