import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsClassSelOfRowL
import Development.AutomorphicArithmetic.CharacterBoxes.ObjCTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AddLargeBaseCoreSlotStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemberTopFinalContextParameters
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace UpperTheory.Top

theorem classSel : StandardLattice.SiegelMassRatioCM → (∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) → ∀ (KP : ∀ B : Base, Fr B.toPre → Prop) (Q Q' : V4.Slot) (Bd : BdT) (Lk : LkT Bd) (H : ∀ 𝒜 : FamClass, RawSel Bd 𝒜 → Prop) (cT : ℝ → ℝ → ℝ), (DC.MinkDiv → GroupRetwisting.BaseCond KP ∧ GroupRetwisting.FirstG KP Q ∧ GroupRetwisting.ExportF KP Q ∧ GroupRetwisting.SecondG KP Q Q') → ExBL KP Q Q' Lk → RowL KP Q Q' Lk H → ∃ (𝒜 : FamClass) (σ : RawSel Bd 𝒜), (DC.MinkDiv → ExD 𝒜 cT) ∧ (∀ (eps : ℝ) (Fm : FamP eps), 𝒜 Fm → DQ.Duty7 Fm ∧ DQ.MtStableF Fm) ∧ IsSel Q' Lk (fun _ _ _ _ _ => True) 𝒜 σ ∧ H 𝒜 σ := by
  intro h1 h2 KP Q Q' Bd Lk H cT hc hx hr
  obtain ⟨R, r, hx', hr'⟩ := RowL.elim hx hr
  obtain ⟨E, hE, hH⟩ := Row.elim hx' hr'
  have hs : IsSel (sAnd Q' R) Lk (fun _ _ _ _ _ => True) (cls (sAnd Q' R) Lk E) (pick (sAnd Q' R) Lk E) :=
    IsSel.mono (fun _ _ _ _ _ _ => trivial) (pick_isSel (sAnd Q' R) Lk E)
  refine ⟨cls (sAnd Q' R) Lk E, pick (sAnd Q' R) Lk E, ?_, fun _ _ h => sevenDuties_of_class h,
    @isSel_of_sAnd Bd Q' R Lk _ (cls (sAnd Q' R) Lk E) (pick (sAnd Q' R) Lk E) hs, hH⟩
  refine recS (QOf (sAnd Q' R) Lk E) cT fun hm => ?_
  obtain ⟨a, b, c, d⟩ := hc hm
  have d' := GlobalTheory.T.secondG_sAnd_of_largeBase KP Q Q' R a (evG_of_ev r) d
  have h := memberTop_final_contextParameters h1 h2 KP Q (sAnd Q' R) (QOf (sAnd Q' R) Lk E) a b c d' hE
  have e : ∀ κ : Par, (fun D O => κ.Pos → QOf (sAnd Q' R) Lk E κ D O) = QOf (sAnd Q' R) Lk E κ :=
    fun κ => funext fun _ => funext fun _ => propext ⟨fun h' h0 => h' h0 h0, fun h' _ => h'⟩
  simpa only [e] using h

end UpperTheory.Top
