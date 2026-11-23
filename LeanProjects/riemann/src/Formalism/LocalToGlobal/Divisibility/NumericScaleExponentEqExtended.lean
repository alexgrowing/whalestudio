import Mathlib
import Formalism.LocalToGlobal.Divisibility.ZscOfNum
import Formalism.LocalToGlobal.Divisibility.HeckeRI

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions

section Scale3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

def ZscOfNum3 (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum)
    (eJ : A3.fam3.base3.J ≃ Fin Nd.R.m) (Nc : ℝ) (Zs : DefSub A3.fam3.amb3) : IndefScale A3.fam3.base3 where
  F0 := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).F0
  J0 := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).J0
  E1u := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).E1u
  l3m := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).l3m
  l3u := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).l3u
  l6m := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).l6m
  l6u := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).l6u
  x := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).x
  b := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).b
  la := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).la
  de := (ZscOfNum A3.A P0 ψ0 Nd eJ Nc (A3.fam3.toSub2 Zs)).de

variable (A3 : FamIn3 K G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (Nd : NumDatum)
  (eJ : A3.fam3.base3.J ≃ Fin Nd.R.m) (Nc : ℝ)

theorem ZscOfNum3_units (Zs : DefSub A3.fam3.amb3) :
    (ZscOfNum3 A3 P0 ψ0 Nd eJ Nc Zs).E1u = Nd.unitE Nc ∧
      (ZscOfNum3 A3 P0 ψ0 Nd eJ Nc Zs).l3u = Nd.B0 * Real.log (Real.log Nd.sc.x) ∧
      (ZscOfNum3 A3 P0 ψ0 Nd eJ Nc Zs).l6u = (Nd.R.f : ℝ) * (Nd.R.nV : ℝ) ^ 2 * Nd.Lp ∧
      (ZscOfNum3 A3 P0 ψ0 Nd eJ Nc Zs).x = Nd.sc.x ∧ (ZscOfNum3 A3 P0 ψ0 Nd eJ Nc Zs).b = Nd.sc.b ∧
      (ZscOfNum3 A3 P0 ψ0 Nd eJ Nc Zs).la = Real.log (Fintype.card G) ∧
      (ZscOfNum3 A3 P0 ψ0 Nd eJ Nc Zs).de = 8 * (Nd.R.f : ℝ) * (Nd.R.r : ℝ) / ((min (Nd.g 0) (Nd.g 1) : ℕ) : ℝ) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Scale3

end Formalism.L2.DIV

end
