import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.Struct

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound.LeadingTermValuation

open PI.UnitaryGroupMassFormula.PadicGainBound

variable {Kc : Type} [Field Kc] {Sh : Shape}

def Lt (t : UV Sh) (F : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc)) : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  MvPowerSeries.pderiv (MvPolynomial Sh.FrV Kc) (Sum.inr t) F -
    ∑ a : Fin Sh.r0, MvPowerSeries.C (MvPolynomial.X (⟨t.1, (t.2.1, 0, a)⟩ : Sh.FrV)) *
      MvPowerSeries.pderiv (MvPolynomial Sh.FrV Kc) (Sum.inl ⟨t.1, (t.2.1, a, t.2.2)⟩) F

end PI.UnitaryGroupMassFormula.PadicGainBound.LeadingTermValuation
