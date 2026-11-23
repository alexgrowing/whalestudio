import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition

namespace UpperTheory.Et

open GlobalTheory.EtC

structure Base : Prop where
  a1 : GlobalTheory.EtC.A1
  a2 : GlobalTheory.EtC.A2
  a3 : GlobalTheory.EtC.A3
  a4 : GlobalTheory.EtC.A4
  a5 : GlobalTheory.EtC.A5
  a6nat : GlobalTheory.EtC.DivisorNaturality
  a6ring : GlobalTheory.EtC.DivisorRingCompatibility
  a6supp : GlobalTheory.EtC.DivisorSupportCondition
  a6add : GlobalTheory.EtC.DivisorAdditivity
  a7 : GlobalTheory.EtC.A7
  a8 : GlobalTheory.EtC.A8
  a9 : GlobalTheory.EtC.A9
  a10 : GlobalTheory.EtC.A10
  a11 : GlobalTheory.EtC.A11
  b1 : GlobalTheory.EtC.B1
  b2 : GlobalTheory.EtC.B2
  b3 : GlobalTheory.EtC.B3
  b4 : GlobalTheory.EtC.B4
  b5 : GlobalTheory.EtC.B5
  b6pic : GlobalTheory.EtC.DivisorPicardCompatibility
  b6h1 : GlobalTheory.EtC.B6h1
  b7 : GlobalTheory.EtC.B7
  c1 : GlobalTheory.EtC.C1
  c2 : GlobalTheory.EtC.C2
  c3 : GlobalTheory.EtC.C3
  c4 : GlobalTheory.EtC.C4
  c5 : GlobalTheory.EtC.C5
  d1 : GlobalTheory.EtC.D1
  d2 : GlobalTheory.EtC.D2
  d3 : GlobalTheory.EtC.D3
  e1 : GlobalTheory.EtC.E1
  e2 : GlobalTheory.EtC.E2
  e3 : GlobalTheory.EtC.E3
  e4 : GlobalTheory.EtC.E4
  e6 : GlobalTheory.EtC.E6
  e8 : GlobalTheory.EtC.E8

end UpperTheory.Et
