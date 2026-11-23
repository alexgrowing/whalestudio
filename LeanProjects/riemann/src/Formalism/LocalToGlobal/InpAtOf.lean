import Formalism.LocalToGlobal.PtKOfReal
import Formalism.LocalToGlobal.Divisibility.SumLeEtaSumNum

noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.L2.RowDataTransport

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

theorem inpAt_of [IsTotallyComplex D.what₂.LL] {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {X : Formalism.L2.Col.Fields}
    {e : X.Tau → (X.E →+* D.what₂.LL)} {c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs}
    {Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)} {Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : RealT Rc P c.face Sp Zsc S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P c.face Sp Zsc) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P c.face Sp Zsc) Cl CHl)
    (Del h0 : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1)
    (Ce : ℝ) (hDIV : ∀ j ∈ SizeData₂.lifts D, Formalism.MainNotions.DIVinN_at L j Ce)
    (hTw : TieTwRec L (pkOf Q hOk hsep Cl CHl hP hI).core.base.Tw)
    (hD : D.what₂.D0 = (P.A3.A.fam.R P.A3.A.fam.μ0).dZ (P.A3.A.fam.lvl P.P0 P.ψ0)
      ((pkOf Q hOk hsep Cl CHl hP hI).Zs.Z P.A3.A.fam.μ0))
    (h11 : LiftExponentAtTwisted P.A3.A P.P0 P.ψ0 (P.A3.fam3.toSub2 (pkOf Q hOk hsep Cl CHl hP hI).Zs)
      (pkOf Q hOk hsep Cl CHl hP hI).core.base.μ (pkOf Q hOk hsep Cl CHl hP hI).core.base.Tw
      (Zsc (pkOf Q hOk hsep Cl CHl hP hI).Zs).J0)
    (hdgA : ∃ dg : ℕ, 0 < dg ∧ (∀ j t, (P.A3.A.fam.L j t).DG (P.A3.A.fam.lvlA P.P0 P.ψ0) ∣ dg) ∧
      ∀ u, ArithAt P.A3 s P.P0 P.ψ0 P.Ps P.ψs c.face Sp Zsc _ Cl CHl (pkOf Q hOk hsep Cl CHl hP hI)
        (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
        (fun _ => divSize L Ce) dg)
    (what₂ : ∀ (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((c.face (pkOf Q hOk hsep Cl CHl hP hI).Zs).a w) → D.what₂.LL))
      (I : DivisionCompatibilityDataThreeSided D P.A3 P.P0 P.ψ0 P.Ps P.ψs (pkOf Q hOk hsep Cl CHl hP hI).Zs
        (pkOf Q hOk hsep Cl CHl hP hI).core.base.toIndefData (pkOf Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (c.face (pkOf Q hOk hsep Cl CHl hP hI).Zs)),
      DivTied3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs (pkOf Q hOk hsep Cl CHl hP hI).Zs
        (pkOf Q hOk hsep Cl CHl hP hI).core.base.toIndefData (pkOf Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (pkOf Q hOk hsep Cl CHl hP hI).core.cols.col NuC I →
      HEq I P.I → ∀ u, RowsU c (pkOf Q hOk hsep Cl CHl hP hI)
        (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
        (I.wU u) (Cons.nuOf L u (I.eNu u))) :
    InpAt c Q hOk hsep Cl CHl hP hI Del h0 lam0 C0 ce Ch Sw C1 eJ H := by
  intro NuC I hT hI'
  obtain ⟨dg, hdg, hdvd, hA⟩ := hdgA
  have hN := inEta3_num (G := P.Gp) L P.A3 (P0 := P.P0) (ψ0 := P.ψ0) (Zs := (pkOf Q hOk hsep Cl CHl hP hI).Zs)
    (S0 := (pkOf Q hOk hsep Cl CHl hP hI).core.base.toIndefData) (tup := I.tup) Ce hDIV rfl hT.num hTw hD
  have hr := what₂ NuC I hT hI'
  choose ch T hF hrest using hr
  choose X0 hX0 hn hnP cb hrest2 using hrest
  refine ⟨fun u => ((DivisionInputsWithoutNorm.ofRows (hrest2 u).2.2.2 (Formalism.L2.DIV.Cons.sgRec_fin L u) (hrest2 u).2.1 (hrest2 u).2.2.1
      (X0 u) (hX0 u) (ch u) (hn u) (hnP u) (cb u) (hrest2 u).1 h11 dg hdg hdvd (hA u)).toDef hN).toDivInputs0R hOk hsep,
    fun u => T u, fun u => hF u⟩

end Formalism.L2.RowDataTransport

end
