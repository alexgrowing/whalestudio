import Formalism.LocalToGlobal.Divisibility.RecBridgeSel
import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces
import Formalism.LocalToGlobal.IndefiniteReal.TrISepWith
import Formalism.LocalToGlobal.IndefiniteReal.RealTP
import Formalism.LocalToGlobal.GroupLattices.BrTied3Hold
import Formalism.LocalToGlobal.Divisibility.ConstantGeTwentyEightAlt

noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.L2.RowDataTransport

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

theorem rows_heq {P : RowSideFamily ex} {Z1 Z2 : DefSub P.A3.fam3.amb3} (h : Z1 = Z2) (R1 : IndefRows (P.A3.side3 P.P0 P.ψ0 Z1))
    (R2 : IndefRows (P.A3.side3 P.P0 P.ψ0 Z2)) (hd : HEq R1.toIndefData R2.toIndefData) : HEq R1 R2 := by
  subst h
  have h' := eq_of_heq hd
  cases R1
  cases R2
  simp only at h'
  subst h'
  rfl

theorem dcPt_move {P : RowSideFamily ex} (hDc : RowsHoldDcPt3 P) {Z : DefSub P.A3.fam3.amb3} (hZ : Z = P.Zs)
    {S0' : IndefData (P.A3.side3 P.P0 P.ψ0 Z)} {S1' : IndefData (P.A3.side3 P.Ps P.ψs Z)} {Dc' : DefCols (P.A3.side3 P.Ps P.ψs Z)}
    (hD : HEq Dc' P.Dc) (hS0 : HEq S0' P.S0) (hS1 : HEq S1' P.S1)
    {I' : DivisionCompatibilityDataThreeSided D P.A3 P.P0 P.ψ0 P.Ps P.ψs Z S0' S1' ex.p0 Dc'} (hI : HEq I' P.I) :
    ∀ (u : D.what₂.Word) (t : P.A3.fam3.base3.Tup) (x : Fin (Dc'.a (I'.wU u)) → D.what₂.LL)
      (F : Fin ((P.A3.side3 P.Ps P.ψs Z).nV t) → D.what₂.LL),
      D.what₂.embLL (Dc'.Pt (I'.wU u) t x F) =
        D.what₂.perCol u (I'.tup t) (D.jN u (I'.eNu u x)) (I'.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F)) := by
  subst hZ
  obtain rfl := eq_of_heq hD
  obtain rfl := eq_of_heq hS0
  obtain rfl := eq_of_heq hS1
  obtain rfl := eq_of_heq hI
  exact hDc

theorem kap_heq {P : RowSideFamily ex} {Z1 Z2 : DefSub P.A3.fam3.amb3} (h : Z1 = Z2) {S1 : IndefData (P.A3.side3 P.Ps P.ψs Z1)}
    {S2 : IndefData (P.A3.side3 P.Ps P.ψs Z2)} (hS : HEq S1 S2) : S1.κ = S2.κ := by
  subst h
  rw [eq_of_heq hS]

theorem tw_heq {P : RowSideFamily ex} {Z1 Z2 : DefSub P.A3.fam3.amb3} (h : Z1 = Z2) {S1 : IndefData (P.A3.side3 P.P0 P.ψ0 Z1)}
    {S2 : IndefData (P.A3.side3 P.P0 P.ψ0 Z2)} (hS : HEq S1 S2) : S1.Tw = S2.Tw := by
  subst h
  rw [eq_of_heq hS]

abbrev pkOf [IsTotallyComplex D.what₂.LL] {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex}
    {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)}
    {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : RealT Rc P Dcf Spf Zscf S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P Dcf Spf Zscf) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P Dcf Spf Zscf) Cl CHl) :=
  primitivePackageFullHecke hOk hsep Q.Rl (faceT P Dcf Spf Zscf) Q.sEE (hkCan P.A3) Cl CHl Q.charW hP hI

def InpAt [IsTotallyComplex D.what₂.LL] {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {X : Formalism.L2.Col.Fields}
    {e : X.Tau → (X.E →+* D.what₂.LL)} (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs)
    {Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)} {Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : RealT Rc P c.face Sp Zsc S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P c.face Sp Zsc) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P c.face Sp Zsc) Cl CHl)
    (Del h0 : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1) : Prop :=
  ∀ (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((c.face (pkOf Q hOk hsep Cl CHl hP hI).Zs).a w) → D.what₂.LL))
      (I : DivisionCompatibilityDataThreeSided D P.A3 P.P0 P.ψ0 P.Ps P.ψs (pkOf Q hOk hsep Cl CHl hP hI).Zs
        (pkOf Q hOk hsep Cl CHl hP hI).core.base.toIndefData (pkOf Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (c.face (pkOf Q hOk hsep Cl CHl hP hI).Zs)),
      DivTied3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs (pkOf Q hOk hsep Cl CHl hP hI).Zs
        (pkOf Q hOk hsep Cl CHl hP hI).core.base.toIndefData (pkOf Q hOk hsep Cl CHl hP hI).core.cols.toIndefData ex.p0
        (pkOf Q hOk hsep Cl CHl hP hI).core.cols.col NuC I →
      HEq I P.I →
      ∃ inp : ∀ u, DivInputs0R (pkOf Q hOk hsep Cl CHl hP hI).core
          (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
          (I.wU u) (Cons.nuOf L u (I.eNu u)) (sgRec L u),
        ∃ hQ : ∀ u, ChainTie (inp u).ch (c.memQ (I.wU u)), ∀ u, FirstCols c.hE (hQ u)

theorem pt_of_real [IsTotallyComplex D.what₂.LL] (Rc : Formalism.L2.RecT ex) (P : RowSideFamily ex) (hpin : RowSideDetermined Rc.T P)
    (hkap : RowsHoldKap3 P) (hPt : RowsHoldDcPt3 P)
    (hR : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I)
    (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL)) (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs)
    (Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)) (hCT : ColTie3 P X e c Sp) (hCTT : ColTieT Rc.T P X e c)
    (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc)
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Q : RealT Rc P c.face Sp Zsc S Ks) {s : ℕ} (hOk : P.A3.fam3.Ok3 s) (hsep : P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT P c.face Sp Zsc) Q.sEE (hkCan P.A3) Cl CHl) (hI : PassIn3 Q.Rl (faceT P c.face Sp Zsc) Cl CHl)
    (hbu : D.BuRational) (C Cabs : ℝ) (Del h0 : ℕ) (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ))
    (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1)
    (hInp : InpAt c Q hOk hsep Cl CHl hP hI Del h0 lam0 C0 ce Ch Sw C1 eJ H)
    (hN : NprimeDef D L) (hh : ∀ u, D.div.h u = hExpl6 D L Y Ch u)
    (hF : FTie L ((Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs c.face Sp Zsc (pkOf Q hOk hsep Cl CHl hP hI).Zs).Z.num Cl CHl) eJ)
    (hC0 : 0 ≤ C) (hC1 : 50 * C0 + 10 ≤ C) (hC2 : 60 * ce ≤ C) (hCabs : 1 ≤ Cabs) (hLa : 0 ≤ L.La) :
    Nonempty (DivisionPackageColumns (DivisionRowsColumns.split_model_to_place_model (L := L) P (Q.rowsHold hOk hsep Cl CHl hP hI hbu).toRowsHold0_3 X e c Sp Zsc) C Cabs) := by
  have hr := Q.rowsHold hOk hsep Cl CHl hP hI hbu
  have hZs : (pkOf Q hOk hsep Cl CHl hP hI).Zs = P.Zs := Q.zs
  have hS0 : HEq (pkOf Q hOk hsep Cl CHl hP hI).core.base.toIndefData P.S0 := Q.s0
  have hS1 : HEq (pkOf Q hOk hsep Cl CHl hP hI).core.cols.toIndefData P.S1 := Q.s1
  have hRows : HEq (pkOf Q hOk hsep Cl CHl hP hI).core.base.toIndefRows (Classical.choose hr.rows0) :=
    rows_heq hZs _ _ (hS0.trans (heq_of_eq (Classical.choose_spec hr.rows0).symm))
  have hDc : HEq (c.face (pkOf Q hOk hsep Cl CHl hP hI).Zs) P.Dc := (congr_arg_heq c.face hZs).trans (heq_of_eq hCT.1)
  exact pkg_of_rows Rc.T P hr X e c Sp Zsc hCT hCTT hR C Cabs Cl CHl _ (pkOf Q hOk hsep Cl CHl hP hI) hZs hRows hS1 Q.col
    Del h0 lam0 C0 ce Ch Sw C1 eJ H
    (fun NuC I hT hI' => ⟨Formalism.L2.G.ServJointF.brTied_of hT ⟨s, hOk.ok2⟩ (dcPt_move hPt hZs hDc hS0 hS1 hI'),
      hInp NuC I hT hI'⟩)
    hN Y (fun σ => (hkap σ).trans (congrFun (kap_heq hZs hS1) _).symm) (fun u => ⟨rfl, HEq.rfl, rfl, hDel, hh0⟩) hh hF
    hC0 hC1 hC2 hCabs hLa

theorem ptK_of_real [IsTotallyComplex D.what₂.LL] (Rc : Formalism.L2.RecT ex) (R : DivisionRowsKernel ex) (hT : R.T = Rc.T)
    (hpin : RowSideDetermined Rc.T R.P) (hkap : RowsHoldKap3 R.P) (hPt : RowsHoldDcPt3 R.P)
    (hR : DivRows3 D R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.P.Zs R.P.S0 R.P.S1 ex.p0 R.P.C R.P.NuC R.P.I) (S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc) {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : RealT Rc R.P R.c.face R.Sp R.Zsc S Ks) (hsep : R.P.A3.fam3.TypesSep3) (Cl CHl : ℝ)
    (hP : CovolumeOntoIsometryConditions Q.Rl (faceT R.P R.c.face R.Sp R.Zsc) Q.sEE (hkCan R.P.A3) Cl CHl)
    (hI : PassIn3 Q.Rl (faceT R.P R.c.face R.Sp R.Zsc) Cl CHl)
    (C Cabs : ℝ) (Del h0 : ℕ) (hDel : D.s.Del = (Del : ℚ)) (hh0 : L.etaSz = (D.R.m : ℝ) * (h0 : ℝ))
    (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : R.P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1)
    (hInp : InpAt R.c Q R.ok1 hsep Cl CHl hP hI Del h0 lam0 C0 ce Ch Sw C1 eJ H)
    (hN : NprimeDef D L) (hh : ∀ u, D.div.h u = hExpl6 D L Y Ch u)
    (hF : FTie L ((Formalism.IndefR.Cx.faceOf3 R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.c.face R.Sp R.Zsc
      (pkOf Q R.ok1 hsep Cl CHl hP hI).Zs).Z.num Cl CHl) eJ)
    (hC0 : 0 ≤ C) (hC1 : 50 * C0 + 10 ≤ C) (hC2 : 60 * ce ≤ C) (hCabs : 1 ≤ Cabs) (hLa : 0 ≤ L.La) :
    Nonempty (DivisionPackageKernel R C Cabs) := by
  have hZs : (pkOf Q R.ok1 hsep Cl CHl hP hI).Zs = R.P.Zs := Q.zs
  have hS0 : HEq (pkOf Q R.ok1 hsep Cl CHl hP hI).core.base.toIndefData R.P.S0 := Q.s0
  have hS1 : HEq (pkOf Q R.ok1 hsep Cl CHl hP hI).core.cols.toIndefData R.P.S1 := Q.s1
  have hRows : HEq (pkOf Q R.ok1 hsep Cl CHl hP hI).core.base.toIndefRows (Classical.choose R.hr.rows0) :=
    rows_heq hZs _ _ (hS0.trans (heq_of_eq (Classical.choose_spec R.hr.rows0).symm))
  have hDc : HEq (R.c.face (pkOf Q R.ok1 hsep Cl CHl hP hI).Zs) R.P.Dc :=
    (congr_arg_heq R.c.face hZs).trans (heq_of_eq R.colTie.1)
  exact pkg_of_rowsK R hR C Cabs Cl CHl _ (pkOf Q R.ok1 hsep Cl CHl hP hI) hZs hRows hS1 Q.col
    Del h0 lam0 C0 ce Ch Sw C1 eJ H
    (fun NuC I hT' hI' => ⟨Formalism.L2.G.ServJointF.brTied_of hT' ⟨1, R.ok1.ok2⟩ (dcPt_move hPt hZs hDc hS0 hS1 hI'),
      hInp NuC I hT' hI'⟩)
    hN Y (fun σ => (hkap σ).trans (congrFun (kap_heq hZs hS1) _).symm) (fun u => ⟨rfl, HEq.rfl, rfl, hDel, hh0⟩) hh hF
    hC0 hC1 hC2 hCabs hLa

def RowsU [IsTotallyComplex D.what₂.LL] {P : RowSideFamily ex} {X : Formalism.L2.Col.Fields}
    {e : X.Tau → (X.E →+* D.what₂.LL)} (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs)
    {Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)} {Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {cf : ConvFace P.A3.fam3.base3} {Cl CHl : ℝ}
    (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs c.face Sp Zsc) cf Cl CHl)
    {Pl : Type} [Fintype Pl] [DecidableEq Pl] (R : RecNums P.A3.fam3.base3.J Pl) (w : (c.face Pk.Zs).Mem)
    (Nu : Submodule (𝓞 D.what₂.LL) (Fin ((c.face Pk.Zs).a w) → D.what₂.LL)) : Prop :=
  ∃ (ch : ColChain (c.face Pk.Zs) w) (T : ChainTie ch (c.memQ w)), FirstCols c.hE T ∧
    ∃ (X0 : InfinitePlace D.what₂.LL → Matrix (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0))
        (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) ℂ)
      (_ : ∀ v, IsUnit (X0 v).det ∧
        ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding)
      (hn : HtNums R (InfinitePlace D.what₂.LL))
      (_ : ∀ v, Formalism.HN.opNormAt (Pi.basisFun D.what₂.LL (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm))
        (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0))).dualBasis
          (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn)
      (cb : CBData ch.X ch.Kj),
      (∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v) ∧
      (∀ v, IsUnit ((c.face Pk.Zs).Xc w v).det) ∧ 0 < (c.face Pk.Zs).a w ∧ Submodule.IsLattice D.what₂.LL Nu

end Formalism.L2.RowDataTransport

end
