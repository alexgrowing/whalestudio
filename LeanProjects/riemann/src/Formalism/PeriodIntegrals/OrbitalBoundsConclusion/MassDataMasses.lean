import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.FundamentalDomainOfCompactOpen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ContinuousCrdAllSymm

open Formalism.L2.SG.TypedSets

theorem massDataMasses_of' (hH : MassDataMassesW.HinfCompact) (hK : MassDataMassesW.KCompactOpen)
    (hC : MassDataMassesW.ClassFinite) (hSA : MassDataMassesW.StrongApproxN) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InMassesAt X hb hK FdN FdN' u u' X0 L A :=
  MassDataMassesW.massDataMasses_of_strongApprox hH hK hC hSA (MassDataMassesW.fundamental_domain_of_compact_open hK MassDataMassesW.nRatBridge_holds)

theorem masses_at_instance (hH : MassDataMassesW.HinfCompact) (hC : MassDataMassesW.ClassFinite)
    (hSA : MassDataMassesW.StrongApproxN) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InMassesAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X
  exact massDataMasses_of' hH MassDataMassesW.kCompactOpen_holds hC hSA X
