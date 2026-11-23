import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MassDataMassesOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MassHNonneg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.EllipticCentralizerQuotientCompact

open Formalism.L2.SG.TypedSets

namespace MassDataMassesW

theorem massDataMasses_of_strongApprox (hH : HinfCompact) (hK : KCompactOpen) (hC : ClassFinite) (hSA : StrongApproxN)
    (h3 : UnipotentFundamentalDomain) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InMassesAt X hb hK FdN FdN' u u' X0 L A :=
  massDataMasses_of (massAll_of hH hK hC) (nVolAll_of hSA splitIso_holds h3 (elliptic_centralizer_quotient_compact hK) n4cov_holds)

end MassDataMassesW
