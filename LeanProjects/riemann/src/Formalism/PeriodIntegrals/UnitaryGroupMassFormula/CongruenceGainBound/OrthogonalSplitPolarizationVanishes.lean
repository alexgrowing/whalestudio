import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CongruenceGainBound.OneOfConstantCoeff

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.KernelEntryData Finset PI.PadicCongruence
open Formalism.MainNotions.G hiding al g0 gam lg rho

namespace PI.UnitaryGroupMassFormula.PadicGainBound

section Cong

variable (Sh : Shape) {Kc : Type} [Field Kc] (Oc : Subring Kc)

def Wt (p : ℕ) (TT : ∀ v, Finset (Fin (Sh.n' v))) (v : Fin Sh.nV) (e : Fin (Sh.n' v)) (a : Fin Sh.r0) (b : Fin Sh.r1)
    (D : ℕ) (j : ℕ → ℕ) : MvPowerSeries (AV Sh) (MvPolynomial Sh.FrV Kc) :=
  ∑ l ∈ range (D + 1), MvPowerSeries.C (MvPolynomial.C ((-1 : Kc) ^ l)) *
    (zt p Sh Kc v (FormalGroupSystem.posSub e (2 * l)) (j l) a b + ut p Sh Kc TT v (FormalGroupSystem.posSub e (2 * l)) (j l) a b)

end Cong

section Expand

variable (Sh : Shape) {Kc : Type} [Field Kc]

end Expand

end PI.UnitaryGroupMassFormula.PadicGainBound
