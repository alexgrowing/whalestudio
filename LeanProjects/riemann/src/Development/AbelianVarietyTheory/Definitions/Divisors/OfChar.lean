import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links NumberField

namespace GlobalTheory.ThetaClauses

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure TupCl (R : RealDat D A Ks) : Prop where
  mu_off : R.tup_mu_off
  mu_used : R.tup_mu_used
  mu_ne : R.tup_mu_ne
  mu_conj : R.tup_mu_conj
  mu_on : R.tup_mu_on

structure CharTh (R : RealDat D A Ks) (F : Face D A) : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  thP : R.IsThP
  tup : TupCl R

end GlobalTheory.ThetaClauses
