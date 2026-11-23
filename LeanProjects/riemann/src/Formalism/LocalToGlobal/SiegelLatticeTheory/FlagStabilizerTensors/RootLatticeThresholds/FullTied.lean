import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FullExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalAdditiveCharContinuous
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUnram

noncomputable section

open scoped Classical TensorProduct
open Matrix
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FullLocalDualAgreement

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocalDualAgreement : Prop :=
  ∀ D : D7, Formalism.L2.SG.Pf.LocCP.LocTied D → ∃ (δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp)
    (M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p) ∧
    ∀ (p : Formalism.MainNotions.S.LocalSplitGroups.PlF D) (i : Fin 2), ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal →
      δ p = (D.s.atP p).ιF (((D.host.g 0 : ℕ) : D.host.F) * ((D.host.g 1 : ℕ) : D.host.F) /
        ((D.host.g i : ℕ) : D.host.F))

theorem locCTied_of (h1 : Formalism.L2.SG.Pf.LocCP.LocDualC) (h2 : Formalism.L2.SG.Pf.LocCP.LocUnramC)
    (h4 : Formalism.L2.SG.Pf.LocCP.LocHaarC) : LocalDualAgreement := fun D hT => by
  obtain ⟨δ, M, hA, hpin⟩ := Formalism.L2.SG.Pf.LocCP.locBody_of D hT h1 h2 Formalism.L2.SG.Pf.LocCP.locPsiContC h4
  exact ⟨δ, M, hA, fun p i hi => hpin p i hi⟩

theorem locCTied_of' (h1 : Formalism.L2.SG.Pf.LocCP.LocDualC) (h4 : Formalism.L2.SG.Pf.LocCP.LocHaarC) : LocalDualAgreement :=
  locCTied_of h1 Formalism.L2.SG.Pf.LocUnramP.locUnramC h4

theorem locDualC_of' (hG : Formalism.L2.SG.Pf.LocCP.LocDualGenC) (hP : Formalism.L2.SG.Pf.LocCP.PinHostC) :
    Formalism.L2.SG.Pf.LocCP.LocDualC :=
  Formalism.L2.SG.Pf.LocCP.locDualC_of hG Formalism.L2.SG.Pf.LocUnramP.locUnramC hP

end Formalism.L2.SG.Pf.FullLocalDualAgreement

namespace Formalism.L2.SG.Pf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem fullExists_tied (h1 : TRExistsC) (hR : LatticeRowBijectionClassFinite) (hL : FullLocalDualAgreement.LocalDualAgreement) :
    ∀ (D : D7) (X : HidaSetting D), X.LevelSubgroupCharacter → Formalism.L2.SG.Pf.LocCP.LocTied D → Nonempty (Full X) := by
  intro D X hK hT
  have hRS : RowStepsC := rowStepsC_of (fun D X hK u =>
    let ⟨a2, a3, a4, a5⟩ := hR D X hK u
    ⟨latSub X u, latRow_of X u a2, a3, a4, classFin_of X u hK a5, gamIsom_of X (inclInj_holds X) u⟩)
  obtain ⟨TR, hTR⟩ := h1 D X hK
  have h2 : ∀ u : D.what₂.Word, ∃ what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V), IsRowReps D (X.Fu u) what₂ ∧
      (∀ Λ ∈ what₂, Formalism.L2.SG.Saturated.IsSplitRow D (X.Fu u) Λ) ∧ ∃ cs : ColSys X u what₂, ColReps hK cs := by
    intro u
    obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := hRS D X hK u
    exact rowsCols_of X u hK a0 a1 a2 a3 a4 a5 a6
  choose what₂ hrows hsplit cs hcs using h2
  choose Dt hDt using fun u => repsExist X u
  choose FN hFN using fundNC_holds D X hK
  obtain ⟨δ, M, hag, hpin⟩ := hL D hT
  exact ⟨⟨hK, TR, hTR, what₂, hrows, hsplit, cs, hcs, Dt, hDt, FN, hFN, δ, M, hag, hpin⟩⟩

end Formalism.L2.SG.Pf
