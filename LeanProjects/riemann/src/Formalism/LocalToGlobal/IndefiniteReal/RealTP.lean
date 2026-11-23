import Formalism.LocalToGlobal.IndefiniteReal.TrISepWith

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

namespace RealT

variable {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : RealT Rc P Dcf Spf Zscf S Ks)

theorem rows_transport {Z Z' : DefSub P.A3.fam3.amb3} (h : Z = Z') (R0 : IndefRows (P.A3.side3 P.P0 P.ψ0 Z))
    (S : IndefData (P.A3.side3 P.P0 P.ψ0 Z')) (hS : HEq R0.toIndefData S) :
    ∃ R0' : IndefRows (P.A3.side3 P.P0 P.ψ0 Z'), R0'.toIndefData = S := by
  subst h
  exact ⟨R0, eq_of_heq hS⟩

theorem rowsHold0 {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (hP : PrimRows3 R.Rl R.F) :
    RowsHold0_3 P := by
  have hR := complex_data_conditions_base_level_of_primitive_links hOk hsep R.charW hP
  refine ⟨R.zs ▸ hR.stable, R.zs ▸ hR.inBlock, ?_, ⟨s, hOk⟩, hsep⟩
  exact rows_transport R.zs (primRows3 hOk hsep R.Rl R.F R.charW hP) P.S0 (by
    rw [primRows3_data]
    exact R.s0)

theorem level_transport {Z : DefSub P.A3.fam3.amb3} (hZ : Z = P.Zs) (S0 : IndefData (P.A3.side3 P.P0 P.ψ0 Z))
    (S1 : IndefData (P.A3.side3 P.Ps P.ψs Z)) (h0 : HEq S0 P.S0) (h1 : HEq S1 P.S1) (h : LevelLink S0 S1) :
    LevelLink P.S0 P.S1 := by
  subst hZ
  cases eq_of_heq h0
  cases eq_of_heq h1
  exact h

theorem cols_transport {Z : DefSub P.A3.fam3.amb3} (hZ : Z = P.Zs) {Dc' : DefCols (P.A3.side3 P.Ps P.ψs Z)} {Sp' : SPer Dc'}
    {N : IndefNum P.A3.fam3.base3} (Sc : IndefColsR (P.A3.side3 P.Ps P.ψs Z) Dc' Sp' N) (hDc : HEq Dc' P.Dc) (hSp : HEq Sp' P.Sp)
    (hS : HEq Sc.toIndefData P.S1) (hC : HEq Sc.col P.C) :
    ∃ (N : IndefNum P.A3.fam3.base3) (Sc : IndefColsR (P.A3.side3 P.Ps P.ψs P.Zs) P.Dc P.Sp N),
      Sc.toIndefData = P.S1 ∧ HEq Sc.col P.C := by
  subst hZ
  cases eq_of_heq hDc
  cases eq_of_heq hSp
  exact ⟨N, Sc, eq_of_heq hS, hC⟩

theorem rowsHold [IsTotallyComplex D.what₂.LL] {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (C CH : ℝ)
    (hP : CovolumeOntoIsometryConditions R.Rl R.F R.sEE (hkCan P.A3) C CH) (hI : PassIn3 R.Rl R.F C CH) (hbu : D.BuRational) :
    RowsHold3 P := by
  let Pk := primitivePackageFullHecke hOk hsep R.Rl R.F R.sEE (hkCan P.A3) C CH R.charW hP hI
  refine ⟨R.rowsHold0 hOk hsep hP.toPrimRows3, ?_, hbu, ?_⟩
  · exact level_transport R.zs _ _ R.s0 R.s1 Pk.core.extra.level
  · have hDc : HEq (Dcf (R.Rl.toCx3 R.F).zs) P.Dc := by
      have h : HEq (Dcf (R.Rl.toCx3 R.F).zs) (Dcf P.Zs) := congr_arg_heq Dcf R.zs
      exact h.trans (heq_of_eq R.dc)
    have hSp : HEq (Spf (R.Rl.toCx3 R.F).zs) P.Sp := by
      have h : HEq (Spf (R.Rl.toCx3 R.F).zs) (Spf P.Zs) := congr_arg_heq Spf R.zs
      exact h.trans R.sp
    exact cols_transport R.zs Pk.core.cols hDc hSp R.s1 R.col

end RealT

end Formalism.IndefR
