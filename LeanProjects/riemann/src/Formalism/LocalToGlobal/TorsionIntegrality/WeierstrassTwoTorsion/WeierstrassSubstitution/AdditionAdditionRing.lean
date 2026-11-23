import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowDouble

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

namespace PlusR

abbrev P7 : Type := MvPolynomial (Fin 7) ℤ

abbrev dX : P7 := MvPolynomial.X 3 - MvPolynomial.X 5

abbrev Univ : Type := Localization.Away dX

theorem dX_ne_zero : dX ≠ 0 :=
  sub_ne_zero.mpr fun h => absurd (MvPolynomial.X_injective h) (by decide)

theorem powers_le : Submonoid.powers dX ≤ nonZeroDivisors P7 :=
  powers_le_nonZeroDivisors_of_noZeroDivisors dX_ne_zero

instance : IsDomain Univ := IsLocalization.isDomain_localization powers_le

instance : CharZero Univ :=
  charZero_of_injective_algebraMap (IsLocalization.injective Univ powers_le)

def v (i : Fin 7) : Univ := algebraMap P7 Univ (MvPolynomial.X i)

def T : Univ := IsLocalization.Away.invSelf dX

def e (x y : Univ) : Univ := y ^ 2 + v 0 * x * y + v 2 * y - x ^ 3 - v 1 * x ^ 2

def WU : WeierstrassCurve Univ :=
  ⟨v 0, v 1, v 2, T * (e (v 3) (v 4) - e (v 5) (v 6)),
    e (v 3) (v 4) - T * (e (v 3) (v 4) - e (v 5) (v 6)) * v 3⟩

end PlusR

end Formalism.L2.Th1.A
