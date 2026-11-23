import Formalism.LocalToGlobal.InertKernelTheory.DefsRep

noncomputable section

namespace Formalism.L2.KerInert.Rep

def sclY {σ R : Type} [CommRing R] (c : R) (G : MvPowerSeries σ R) : MvPowerSeries σ R :=
  MvPowerSeries.subst (fun k : σ => MvPowerSeries.C c * MvPowerSeries.X k) G

end Formalism.L2.KerInert.Rep
