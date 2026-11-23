import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.StrongApproxN

open Formalism.L2.SG.TypedSets

namespace MassDataMassesW

theorem massDataMasses_of (hM : MassAll) (hN : NVolAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InMassesAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hX
  obtain ⟨hT, hL, hF, hF'⟩ := hX
  exact ⟨hM X hb u hT, hN X hb hK u FdN hT hL hF, hM X hb u' hT, hN X hb hK u' FdN' hT hL hF'⟩

end MassDataMassesW
