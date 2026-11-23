import Formalism.LocalToGlobal.CharacterGerms.CoordinatePointConstantCoeff
import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroSecondCoordinate

set_option autoImplicit false

noncomputable section

open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UnitSeriesFrobeniusLemmas

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries PartialDerivEval LMulP

section Gen

variable {C : Type} [Field C] {V : VF C}

end Gen

section Main

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {d : ℕ}
  (Y : FBChart C V O d)

def Lz : Pt C 2 d := comp1 (Y.nmul V.l) (pt C d 1)

theorem hz1 : Z0 (![pt C d 1] : Fin 1 → Pt C 2 d) := z0_1 _ fun i => z0_pt 1 i

def EL : Fin 2 → Pt C 2 d := ![pt C d 0, Lz Y]

def Mz (j k : Fin d) : PS C 2 d := ev (n := 2) ![pt C d 1, 0] (pderiv C ((1 : Fin 2), k) (Y.B.G.F j))

def Gk (k : Fin d) : PS C 2 d :=
  (∑ j, Mz Y j k * pderiv C ((1 : Fin 2), j) Y.h) + ev (n := 2) ![pt C d 0] (Y.sgP (Pi.single k 1))

def HH : PS C 2 d := ev (EL Y) Y.h - MvPowerSeries.C (V.l : C) * Y.h

end Main

end UnitSeriesFrobeniusLemmas

end Formalism.L2.FormalSeriesBounds
