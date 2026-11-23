import Formalism.LocalToGlobal.PtKOfReal
import Formalism.SharpRestriction.Divisibility.HookProducts.SharpFunctionalBoundFamily

noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
  Formalism.L2.RowDataTransport

namespace Formalism.L2.DIV.FunSharpTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

theorem muMax_heq {P : RowSideFamily ex} {Z1 Z2 : DefSub P.A3.fam3.amb3} (h : Z1 = Z2) {S1 : IndefData (P.A3.side3 P.Ps P.ψs Z1)}
    {S2 : IndefData (P.A3.side3 P.Ps P.ψs Z2)} (hS : HEq S1 S2) : S1.muMaxRR = S2.muMaxRR := by
  subst h
  cases hS
  rfl

theorem funSharp_pt [IsTotallyComplex D.what₂.LL] {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : RealT Rc P Dcf Spf Zscf S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P Dcf Spf Zscf) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P Dcf Spf Zscf) Cl CHl)
    (hR : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (hkap : RowsHoldKap3 P)
    (hde0 : 0 ≤ (Zscf (pkOf Q hOk hsep Cl CHl hP hI).Zs).de) (hde : (Zscf (pkOf Q hOk hsep Cl CHl hP hI).Zs).de ≤ 1 / 3) :
    D.div.RR.muMax + meanE D (fun e => Real.log (Y.kapR e)) ≤
      (Zscf (pkOf Q hOk hsep Cl CHl hP hI).Zs).x ^ CHl * (Zscf (pkOf Q hOk hsep Cl CHl hP hI).Zs).b +
        14 * (Zscf (pkOf Q hOk hsep Cl CHl hP hI).Zs).la := by
  have hZs : (pkOf Q hOk hsep Cl CHl hP hI).Zs = P.Zs := Q.zs
  have hS1 : HEq (pkOf Q hOk hsep Cl CHl hP hI).core.cols.toIndefData P.S1 := Q.s1
  have hpass : (pkOf Q hOk hsep Cl CHl hP hI).core.cols.muMaxRR ≤
      (Zscf (pkOf Q hOk hsep Cl CHl hP hI).Zs).x ^ CHl * (Zscf (pkOf Q hOk hsep Cl CHl hP hI).Zs).b -
        meanLog (pkOf Q hOk hsep Cl CHl hP hI).core.base.κ + 14 * (Zscf (pkOf Q hOk hsep Cl CHl hP hI).Zs).la :=
    ((pkOf Q hOk hsep Cl CHl hP hI).core.extra.passage hde0 hde _ (pkOf Q hOk hsep Cl CHl hP hI).core.extra.fun0).1
  have hmu : D.div.RR.muMax = (pkOf Q hOk hsep Cl CHl hP hI).core.cols.muMaxRR :=
    (Formalism.MainNotions.DIV.HookProducts.FunSharp.muMax_tie D.div.RR _ _ P.I.eRR hR.sharpRR.lat hR.sharpRR.metric).symm.trans
      (muMax_heq hZs hS1).symm
  have hκ : meanE D (fun e => Real.log (Y.kapR e)) = meanLog (pkOf Q hOk hsep Cl CHl hP hI).core.base.κ := by
    rw [(pkOf Q hOk hsep Cl CHl hP hI).core.extra.level.2.1]
    exact meanEmb_eq_meanLog _ _ (fun σ => by rw [hkap σ, kap_heq hZs hS1])
  rw [hmu, hκ]
  linarith

end Formalism.L2.DIV.FunSharpTop

end
