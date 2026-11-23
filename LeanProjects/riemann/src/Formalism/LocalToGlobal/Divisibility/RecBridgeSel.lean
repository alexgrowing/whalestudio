import Mathlib
import Formalism.LocalToGlobal.Divisibility.RecBridgeTied
import Formalism.LocalToGlobal.Divisibility.RecBridgeMkF
import Formalism.LocalToGlobal.Columns.RowFormsSym

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.BasicNotions.DV

section Congr

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ} {A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m}
  {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G} {ψs : Ps →* D.what₂.LLˣ} {X0 : Formalism.BasicNotions.BaseLevelRowSide D}

theorem divTied3_congr {Zs Zs' : DefSub A3.fam3.amb3} (hZ : Zs = Zs')
    {S0 : IndefData (A3.side3 P0 ψ0 Zs)} {S0' : IndefData (A3.side3 P0 ψ0 Zs')} (h0 : HEq S0 S0')
    {S1 : IndefData (A3.side3 Ps ψs Zs)} {S1' : IndefData (A3.side3 Ps ψs Zs')} (h1 : HEq S1 S1')
    {Dc : DefCols (A3.side3 Ps ψs Zs)} {Dc' : DefCols (A3.side3 Ps ψs Zs')} (hD : HEq Dc Dc')
    {Sp : SPer Dc} {Sp' : SPer Dc'} (hS : HEq Sp Sp') {C : ColData Dc Sp S1} {C' : ColData Dc' Sp' S1'} (hC : HEq C C')
    {NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)} {I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc}
    (hT : DivTied3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I) :
    ∃ (NuC' : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc'.a u) → D.what₂.LL)) (I' : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs' S0' S1' X0 Dc'),
      DivTied3 D A3 P0 ψ0 Ps ψs Zs' S0' S1' X0 C' NuC' I' ∧ HEq NuC' NuC ∧ HEq I' I := by
  subst hZ
  cases h0
  cases h1
  cases hD
  cases hS
  cases hC
  exact ⟨NuC, I, hT, HEq.rfl, HEq.rfl⟩

end Congr

section Sel

open Formalism.MainNotions Formalism.L2.Rows

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

private theorem exists_heq_of_eq_of_heq {α : Sort*} {β : α → Sort*} {γ : ∀ a, β a → Sort*} {a a' : α} (ha : a = a')
    {b : β a} {b' : β a'} (hb : HEq b b') (x : γ a b) : ∃ y : γ a' b', HEq y x := by
  subst ha
  cases hb
  exact ⟨x, HEq.rfl⟩

theorem ColTie3.transport {P : RowSideFamily ex} {X : Formalism.L2.Col.Fields} {e : X.Tau → (X.E →+* D.what₂.LL)}
    {c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs} {Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)}
    (h : ColTie3 P X e c Sp) (hR : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) :
    ∃ (C' : ColData (c.face P.Zs) (Sp P.Zs) P.S1) (NuC' : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin ((c.face P.Zs).a u) → D.what₂.LL))
      (I' : DivisionCompatibilityDataThreeSided D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 (c.face P.Zs)),
      DivTied3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 C' NuC' I' ∧ HEq C' P.C ∧ HEq NuC' P.NuC ∧ HEq I' P.I := by
  obtain ⟨C', hC'⟩ := exists_heq_of_eq_of_heq (β := fun a => SPer a) (γ := fun a b => ColData a b P.S1) h.1.symm h.2.symm P.C
  obtain ⟨NuC', I', hT', hN, hI⟩ := divTied3_congr (Zs := P.Zs) (Zs' := P.Zs) rfl HEq.rfl HEq.rfl (heq_of_eq h.1.symm)
    h.2.symm hC'.symm (DivTied3.ofSplit P.tied.div hR)
  exact ⟨C', NuC', I', hT', hC', hN, hI⟩

def DivisionPackageColumns.ofTied (P : RowSideFamily ex) (hr : RowsHold0_3 P) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL))
    (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs) (Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs))
    (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (C Cabs Cp CHp : ℝ) (cf : ConvFace P.A3.fam3.base3)
    (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs c.face Sp Zsc) cf Cp CHp)
    (hZs : Pk.Zs = P.Zs) (hRows : HEq Pk.core.base.toIndefRows (Classical.choose hr.rows0))
    (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((c.face Pk.Zs).a w) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D P.A3 P.P0 P.ψ0 P.Ps P.ψs Pk.Zs Pk.core.base.toIndefData Pk.core.cols.toIndefData ex.p0 (c.face Pk.Zs))
    (hT : DivTied3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs Pk.Zs Pk.core.base.toIndefData Pk.core.cols.toIndefData ex.p0 Pk.core.cols.col NuC I)
    (brTied : (Formalism.L2.G.ServJointF.ColBrF.mk P.A3.fam3.base3 (P.A3.side3 P.Ps P.ψs Pk.Zs) (c.face Pk.Zs) I.wU
      (fun u x => I.eNu u x) I.tup (fun t F => I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F)) Pk.core.cols.μ).Tied)
    (Del h0 : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1)
    (inp : ∀ u, DivInputs0R Pk.core
      (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
      (I.wU u) (Cons.nuOf L u (I.eNu u)) (sgRec L u))
    (hQ : ∀ u, ChainTie (inp u).ch (c.memQ (I.wU u))) (h0c : ∀ u, FirstCols c.hE (hQ u))
    (hN : NprimeDef D L) (Z : DivX D) (hk : ∀ σ, Z.kapR σ = Pk.core.cols.κ (InfinitePlace.mk σ))
    (tH : ∀ u, NumRecTieH (ofRecord D L Del h0) L u (letterOf D L Del h0 u) ((D.mem u).A.T) Del h0)
    (hh : ∀ u, D.div.h u = hExpl6 D L Z Ch u)
    (hF : FTie L ((Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs c.face Sp Zsc Pk.Zs).Z.num Cp CHp) eJ)
    (hC0 : 0 ≤ C) (hC1 : 50 * C0 + 10 ≤ C) (hC2 : 60 * ce ≤ C) (hCabs : 1 ≤ Cabs) (hLa : 0 ≤ L.La) :
    DivisionPackageColumns (DivisionRowsColumns.split_model_to_place_model (L := L) P hr X e c Sp Zsc) C Cabs where
  toDivisionPackageFace := DivisionPackageFace.ofOpen (DivisionRowsColumns.split_model_to_place_model (L := L) P hr X e c Sp Zsc).toF C Cabs Cp CHp cf Pk hZs hRows I.wU I.eNu I.eRR NuC
    hT.cols.Nu hT.sharp.RR hT.cols.Bk I.tup (fun t F => I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F)) brTied
    Del h0 lam0 C0 ce Ch Sw C1 eJ H inp hN Z hk tH hh hF hC0 hC1 hC2 hCabs hLa
  hQ := hQ
  h0 := h0c

def ColTieT (T : TiedDataSK ex) (P : RowSideFamily ex) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL))
    (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs) : Prop :=
  T.ker.X = fieldsLL D X e ∧ c.Rk = D.R ∧ HEq c.Pr T.ker.Pr ∧ HEq c.Ch T.ker.Ch ∧ HEq c.sel T.ker.sel ∧ HEq c.Sg T.ker.S ∧
    HEq c.mu (fun t => T.ker.tup (P.I.tup t)) ∧ HEq c.cst (fun t => T.ker.cst (P.I.tup t)) ∧
    HEq c.Li (fun t => T.ker.idx (P.I.tup t)) ∧ c.m2 = T.ker.m2 ∧ HEq c.Gc T.ker.glob ∧
    HEq c.Am (Formalism.L2.Ker.ambOf T.ker.seam T.ker.B T.ker.χ T.ker.cD) ∧ c.Mem = D.what₂.Word ∧ HEq c.wd T.ker.word

private theorem heq_app_of_eq_of_heq {α : Sort*} {β γ : α → Sort*} (f : ∀ a, β a → γ a) {a a' : α} (ha : a = a')
    {x : β a} {y : β a'} (h : HEq x y) : HEq (f a x) (f a' y) := by
  subst ha
  cases h
  exact HEq.rfl

private theorem tied_pkg_lemma_3 (P : RowSideFamily ex) (hr : RowsHold0_3 P) (X : Formalism.L2.Col.Fields)
    (e : X.Tau → (X.E →+* D.what₂.LL)) (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs)
    (Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)) (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3)
    (hCT : ColTie3 P X e c Sp)
    (hR : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) {Cp CHp : ℝ} {cf : ConvFace P.A3.fam3.base3}
    (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs c.face Sp Zsc) cf Cp CHp)
    (hZs : Pk.Zs = P.Zs) (hRows : HEq Pk.core.base.toIndefRows (Classical.choose hr.rows0))
    (hS1 : HEq Pk.core.cols.toIndefData P.S1) (hCol : HEq Pk.core.cols.col P.C) :
    ∃ (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((c.face Pk.Zs).a w) → D.what₂.LL))
      (I : DivisionCompatibilityDataThreeSided D P.A3 P.P0 P.ψ0 P.Ps P.ψs Pk.Zs Pk.core.base.toIndefData Pk.core.cols.toIndefData ex.p0 (c.face Pk.Zs)),
      DivTied3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs Pk.Zs Pk.core.base.toIndefData Pk.core.cols.toIndefData ex.p0 Pk.core.cols.col NuC I ∧
      HEq I P.I := by
  obtain ⟨C', NuC', I', hT', hC', -, hI'⟩ := ColTie3.transport hCT hR
  have h0' : HEq P.S0 Pk.core.base.toIndefData :=
    (heq_of_eq (Classical.choose_spec hr.rows0)).symm.trans
      (heq_app_of_eq_of_heq (fun Z (Q : IndefRows (P.A3.side3 P.P0 P.ψ0 Z)) => Q.toIndefData) hZs.symm hRows.symm)
  obtain ⟨NuC'', I'', hT'', -, hI''⟩ := divTied3_congr hZs.symm h0' hS1.symm (congr_arg_heq c.face hZs.symm)
    (congr_arg_heq Sp hZs.symm) (C' := Pk.core.cols.col) (hC'.trans hCol.symm) hT'
  exact ⟨NuC'', I'', hT'', hI''.trans hI'⟩

theorem pkg_of_rows (T : TiedDataSK ex) (P : RowSideFamily ex) (hr : RowsHold3 P) (X : Formalism.L2.Col.Fields)
    (e : X.Tau → (X.E →+* D.what₂.LL)) (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs)
    (Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)) (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3)
    (hCT : ColTie3 P X e c Sp) (_hCTT : ColTieT T P X e c)
    (hR : DivRows3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs P.Zs P.S0 P.S1 ex.p0 P.C P.NuC P.I) (C Cabs Cp CHp : ℝ) (cf : ConvFace P.A3.fam3.base3)
    (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs c.face Sp Zsc) cf Cp CHp)
    (hZs : Pk.Zs = P.Zs) (hRows : HEq Pk.core.base.toIndefRows (Classical.choose hr.rows0))
    (hS1 : HEq Pk.core.cols.toIndefData P.S1) (hCol : HEq Pk.core.cols.col P.C)
    (Del h0 : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1)
    (hOpen : ∀ (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((c.face Pk.Zs).a w) → D.what₂.LL))
      (I : DivisionCompatibilityDataThreeSided D P.A3 P.P0 P.ψ0 P.Ps P.ψs Pk.Zs Pk.core.base.toIndefData Pk.core.cols.toIndefData ex.p0 (c.face Pk.Zs)),
      DivTied3 D P.A3 P.P0 P.ψ0 P.Ps P.ψs Pk.Zs Pk.core.base.toIndefData Pk.core.cols.toIndefData ex.p0 Pk.core.cols.col NuC I →
      HEq I P.I →
      (Formalism.L2.G.ServJointF.ColBrF.mk P.A3.fam3.base3 (P.A3.side3 P.Ps P.ψs Pk.Zs) (c.face Pk.Zs) I.wU
        (fun u x => I.eNu u x) I.tup (fun t F => I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F)) Pk.core.cols.μ).Tied ∧
      ∃ inp : ∀ u, DivInputs0R Pk.core
          (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
          (I.wU u) (Cons.nuOf L u (I.eNu u)) (sgRec L u),
        ∃ hQ : ∀ u, ChainTie (inp u).ch (c.memQ (I.wU u)), ∀ u, FirstCols c.hE (hQ u))
    (hN : NprimeDef D L) (Z : DivX D) (hk : ∀ σ, Z.kapR σ = Pk.core.cols.κ (InfinitePlace.mk σ))
    (tH : ∀ u, NumRecTieH (ofRecord D L Del h0) L u (letterOf D L Del h0 u) ((D.mem u).A.T) Del h0)
    (hh : ∀ u, D.div.h u = hExpl6 D L Z Ch u)
    (hF : FTie L ((Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs c.face Sp Zsc Pk.Zs).Z.num Cp CHp) eJ)
    (hC0 : 0 ≤ C) (hC1 : 50 * C0 + 10 ≤ C) (hC2 : 60 * ce ≤ C) (hCabs : 1 ≤ Cabs) (hLa : 0 ≤ L.La) :
    Nonempty (DivisionPackageColumns (DivisionRowsColumns.split_model_to_place_model (L := L) P hr.toRowsHold0_3 X e c Sp Zsc) C Cabs) := by
  obtain ⟨NuC', I', hT', hI'⟩ := tied_pkg_lemma_3 P hr.toRowsHold0_3 X e c Sp Zsc hCT hR Pk hZs hRows hS1 hCol
  obtain ⟨brT, inp, hQ, h0c⟩ := hOpen NuC' I' hT' hI'
  exact ⟨DivisionPackageColumns.ofTied P hr.toRowsHold0_3 X e c Sp Zsc C Cabs Cp CHp cf Pk hZs hRows NuC' I' hT' brT Del h0 lam0 C0 ce Ch Sw C1
    eJ H inp hQ h0c hN Z hk tH hh hF hC0 hC1 hC2 hCabs hLa⟩

end Sel

section RowsK

open Formalism.MainNotions Formalism.L2.Rows

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

theorem divTieDat3_heq {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ} {A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {Ps : Subgroup G}
    {ψs : Ps →* D.what₂.LLˣ} {X0 : Formalism.BasicNotions.BaseLevelRowSide D} {Zs Zs' : DefSub A3.fam3.amb3}
    {S0 : IndefData (A3.side3 P0 ψ0 Zs)} {S0' : IndefData (A3.side3 P0 ψ0 Zs')}
    {S1 : IndefData (A3.side3 Ps ψs Zs)} {S1' : IndefData (A3.side3 Ps ψs Zs')}
    {Dc : DefCols (A3.side3 Ps ψs Zs)} {Dc' : DefCols (A3.side3 Ps ψs Zs')}
    {I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc} {I' : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs' S0' S1' X0 Dc'}
    (hZ : Zs = Zs') (h0 : HEq S0 S0') (h1 : HEq S1 S1') (hD : HEq Dc Dc') (h : HEq I I') :
    I.tup = I'.tup ∧ (∀ t y, HEq (I.jA t y) (I'.jA t y)) ∧ ∀ u, HEq (I.wU u) (I'.wU u) := by
  subst hZ
  cases h0
  cases h1
  cases hD
  cases h
  exact ⟨rfl, fun _ _ => HEq.rfl, fun _ => HEq.rfl⟩

structure DivisionRowsKernel (ex : Extra D L hT Gi Gl Kc Y cX) : Type 1 where
  T : TiedDataSK ex
  P : RowSideFamily ex
  hr : RowsHold0_3 P
  X : Formalism.L2.Col.Fields
  e : X.Tau → (X.E →+* D.what₂.LL)
  c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs
  Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)
  Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3
  colTie : ColTie3 P X e c Sp
  kerTie : ColTieT T P X e c
  wTie : ∀ u, HEq (P.I.wU u) u
  lvTie : c.Lv = Formalism.L2.Col.rPsymF (R := c.Rk) c.Ch
  sgTie : c.Am.σ₀ = D.what₂.embLL
  v0 : InfinitePlace D.what₂.LL
  TU : Finset (Tup X.F X.E D.what₂.LL c.Sg)
  xiVal : Tup X.F X.E D.what₂.LL c.Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ
  trIv : Fin c.Rk.m → (Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅ × List ℕ → D.what₂.LL
  famEq : HEq P.A3 (colIn3 c.W c.Ch c.sel c.hX v0 TU c.Xg ∅ xiVal trIv)
  gEq : P.Gp = Formalism.L2.Col.G0 X.E c.Pr.vGs c.Rk.r
  plEq : P.Pl0 = Formalism.L2.Col.LevOff ∅ c.Pr.vGs ∅
  i0Eq : P.I0 = Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅
  tEq : P.T = TupF (X := fieldsLL D X e) TU
  muTie : ∀ t, c.mu t = (cast tEq t).1
  ok1 : P.A3.fam3.Ok3 1

structure SquareIntegrableColumnsCompatible (T : TiedDataSK ex) (P : RowSideFamily ex) : Type 1 where
  X : Formalism.L2.Col.Fields
  e : X.Tau → (X.E →+* D.what₂.LL)
  c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs
  Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)
  colTie : ColTie3 P X e c Sp
  kerTie : ColTieT T P X e c
  wTie : ∀ u, HEq (P.I.wU u) u
  lvTie : c.Lv = Formalism.L2.Col.rPsymF (R := c.Rk) c.Ch
  sgTie : c.Am.σ₀ = D.what₂.embLL
  v0 : InfinitePlace D.what₂.LL
  TU : Finset (Tup X.F X.E D.what₂.LL c.Sg)
  xiVal : Tup X.F X.E D.what₂.LL c.Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ
  trIv : Fin c.Rk.m → (Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅ × List ℕ → D.what₂.LL
  famEq : HEq P.A3 (colIn3 c.W c.Ch c.sel c.hX v0 TU c.Xg ∅ xiVal trIv)
  gEq : P.Gp = Formalism.L2.Col.G0 X.E c.Pr.vGs c.Rk.r
  plEq : P.Pl0 = Formalism.L2.Col.LevOff ∅ c.Pr.vGs ∅
  i0Eq : P.I0 = Formalism.L2.Col.LevOffI ∅ c.Pr.vGs ∅
  tEq : P.T = TupF (X := fieldsLL D X e) TU
  muTie : ∀ t, c.mu t = (cast tEq t).1
  ok1 : P.A3.fam3.Ok3 1

def SquareIntegrableColumnsCompatible.toK {T : TiedDataSK ex} {P : RowSideFamily ex} (K : SquareIntegrableColumnsCompatible T P) (hr : RowsHold0_3 P)
    (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) : DivisionRowsKernel ex where
  T := T
  P := P
  hr := hr
  X := K.X
  e := K.e
  c := K.c
  Sp := K.Sp
  Zsc := Zsc
  colTie := K.colTie
  kerTie := K.kerTie
  wTie := K.wTie
  lvTie := K.lvTie
  sgTie := K.sgTie
  v0 := K.v0
  TU := K.TU
  xiVal := K.xiVal
  trIv := K.trIv
  famEq := K.famEq
  gEq := K.gEq
  plEq := K.plEq
  i0Eq := K.i0Eq
  tEq := K.tEq
  muTie := K.muTie
  ok1 := K.ok1

theorem SquareIntegrableColumnsCompatible.toK_c {T : TiedDataSK ex} {P : RowSideFamily ex} (K : SquareIntegrableColumnsCompatible T P) (hr : RowsHold0_3 P)
    (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) : (K.toK hr Zsc).c = K.c := rfl

def DivisionRowsKernel.toT (R : DivisionRowsKernel ex) : DivisionRowsColumns L :=
  { DivisionRowsColumns.split_model_to_place_model (L := L) R.P R.hr R.X R.e R.c R.Sp R.Zsc with s := 1, hOk := R.ok1 }

theorem DivisionRowsKernel.tied_rows_scale_eq_one (R : DivisionRowsKernel ex) : R.toT.s = 1 := rfl

theorem DivisionRowsKernel.toT_c (R : DivisionRowsKernel ex) : R.toT.c = R.c := rfl

theorem DivisionRowsKernel.toT_toF (R : DivisionRowsKernel ex) : R.toT.toF = (DivisionRowsColumns.split_model_to_place_model (L := L) R.P R.hr R.X R.e R.c R.Sp R.Zsc).toF := rfl

structure DivisionPackageKernel (Q : DivisionRowsKernel ex) (C Cabs : ℝ) extends DivisionPackageColumns Q.toT C Cabs where
  tupTie : ∀ t, tup t = Q.P.I.tup t
  evTie : ∀ t (F : Fin ((Q.P.A3.side3 Q.P.Ps Q.P.ψs Pk.Zs).nV t) → D.what₂.LL),
    HEq (eV t F) (Q.P.I.jA t ((rV0 D Q.P.A3.A Q.P.Ps Q.P.ψs t).mulVec F))
  wuTie : ∀ u, HEq (wU u) u

private theorem eq_app_of_eq_of_heq {α : Sort*} {β : α → Sort*} {γ : Sort*} (f : ∀ a, β a → γ) {a a' : α} (ha : a = a')
    {x : β a} {y : β a'} (h : HEq x y) : f a x = f a' y := by
  subst ha
  cases h
  rfl

theorem DivisionPackageKernel.pin {R : DivisionRowsKernel ex} {C Cabs : ℝ} (Pt : DivisionPackageKernel R C Cabs) (u : D.what₂.Word) (t : R.P.A3.fam3.base3.Tup)
    (x : Fin (ramDim R.c.W R.c.Ch R.c.hX (R.c.wd (Pt.wU u))) → D.what₂.LL)
    (F : Fin ((R.P.A3.side3 R.P.Ps R.P.ψs Pt.Pk.Zs).nV t) → D.what₂.LL) :
    D.what₂.embLL (colPer R.c.hX (R.c.hP t) R.c.Xg (R.c.ker t (Pt.wU u)) (R.c.hF t (Pt.wU u)) (R.c.hL t) (R.c.ev Pt.Pk.Zs t) x F) =
      D.what₂.perCol u (R.P.I.tup t) (D.jN u (Pt.eNu u x)) (R.P.I.jA t ((rV0 D R.P.A3.A R.P.Ps R.P.ψs t).mulVec F)) := by
  exact (Pt.brTied.dcPt u t x F).trans
    (eq_app_of_eq_of_heq (fun a (v : D.what₂.Amb a) => D.what₂.perCol u a (D.jN u (Pt.eNu u x)) v) (Pt.tupTie t) (Pt.evTie t F))

theorem pkg_of_rowsK (R : DivisionRowsKernel ex)
    (hR : DivRows3 D R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.P.Zs R.P.S0 R.P.S1 ex.p0 R.P.C R.P.NuC R.P.I) (C Cabs Cp CHp : ℝ) (cf : ConvFace R.P.A3.fam3.base3)
    (Pk : IndefPkgR R.P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.c.face R.Sp R.Zsc) cf Cp CHp)
    (hZs : Pk.Zs = R.P.Zs) (hRows : HEq Pk.core.base.toIndefRows (Classical.choose R.hr.rows0))
    (hS1 : HEq Pk.core.cols.toIndefData R.P.S1) (hCol : HEq Pk.core.cols.col R.P.C)
    (Del h0 : ℕ) (lam0 C0 ce Ch Sw C1 : ℝ) (eJ : R.P.A3.fam3.base3.J ≃ Fin D.R.m)
    (H : ∀ u, (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 C0 ce Ch Sw C1)
    (hOpen : ∀ (NuC : ∀ w, Submodule (𝓞 D.what₂.LL) (Fin ((R.c.face Pk.Zs).a w) → D.what₂.LL))
      (I : DivisionCompatibilityDataThreeSided D R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs Pk.Zs Pk.core.base.toIndefData Pk.core.cols.toIndefData ex.p0
        (R.c.face Pk.Zs)),
      DivTied3 D R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs Pk.Zs Pk.core.base.toIndefData Pk.core.cols.toIndefData ex.p0 Pk.core.cols.col
        NuC I →
      HEq I R.P.I →
      (Formalism.L2.G.ServJointF.ColBrF.mk R.P.A3.fam3.base3 (R.P.A3.side3 R.P.Ps R.P.ψs Pk.Zs) (R.c.face Pk.Zs) I.wU
        (fun u x => I.eNu u x) I.tup (fun t F => I.jA t ((rV0 D R.P.A3.A R.P.Ps R.P.ψs t).mulVec F)) Pk.core.cols.μ).Tied ∧
      ∃ inp : ∀ u, DivInputs0R Pk.core
          (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) ((D.mem u).A.T) L.Nc lam0 C0 ce Ch Sw C1 (H u))
          (I.wU u) (Cons.nuOf L u (I.eNu u)) (sgRec L u),
        ∃ hQ : ∀ u, ChainTie (inp u).ch (R.c.memQ (I.wU u)), ∀ u, FirstCols R.c.hE (hQ u))
    (hN : NprimeDef D L) (Z : DivX D) (hk : ∀ σ, Z.kapR σ = Pk.core.cols.κ (InfinitePlace.mk σ))
    (tH : ∀ u, NumRecTieH (ofRecord D L Del h0) L u (letterOf D L Del h0 u) ((D.mem u).A.T) Del h0)
    (hh : ∀ u, D.div.h u = hExpl6 D L Z Ch u)
    (hF : FTie L ((Formalism.IndefR.Cx.faceOf3 R.P.A3 R.P.P0 R.P.ψ0 R.P.Ps R.P.ψs R.c.face R.Sp R.Zsc Pk.Zs).Z.num Cp CHp) eJ)
    (hC0 : 0 ≤ C) (hC1 : 50 * C0 + 10 ≤ C) (hC2 : 60 * ce ≤ C) (hCabs : 1 ≤ Cabs) (hLa : 0 ≤ L.La) :
    Nonempty (DivisionPackageKernel R C Cabs) := by
  obtain ⟨NuC', I', hT', hI'⟩ := tied_pkg_lemma_3 R.P R.hr R.X R.e R.c R.Sp R.Zsc R.colTie hR Pk hZs hRows hS1 hCol
  obtain ⟨brT, inp, hQ, h0c⟩ := hOpen NuC' I' hT' hI'
  have hD : HEq (R.c.face Pk.Zs) R.P.Dc := (congr_arg_heq R.c.face hZs).trans (heq_of_eq R.colTie.1)
  have h0' : HEq Pk.core.base.toIndefData R.P.S0 :=
    (heq_app_of_eq_of_heq (fun Z (Q : IndefRows (R.P.A3.side3 R.P.P0 R.P.ψ0 Z)) => Q.toIndefData) hZs hRows).trans
      (heq_of_eq (Classical.choose_spec R.hr.rows0))
  obtain ⟨ht, hj, hw⟩ := divTieDat3_heq hZs h0' hS1 hD hI'
  let Q0 := DivisionPackageColumns.ofTied R.P R.hr R.X R.e R.c R.Sp R.Zsc C Cabs Cp CHp cf Pk hZs hRows NuC' I' hT' brT Del h0 lam0 C0 ce Ch Sw
    C1 eJ H inp hQ h0c hN Z hk tH hh hF hC0 hC1 hC2 hCabs hLa
  exact ⟨⟨⟨Q0.toDivisionPackageFace, Q0.hQ, Q0.h0⟩, congrFun ht, fun t F => hj t _, fun u => (hw u).trans (R.wTie u)⟩⟩

abbrev rowsKtoT {eps : ℝ} {Fm : FamP eps}
    (Rk : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsKernel (Fm.ex x hx i)) :
    Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsColumns (Fm.L x i) :=
  ⟨Rk.1, fun x hx h i => (Rk.2 x hx h i).toT⟩

structure BridgeRowsK {eps : ℝ} (Fm : FamP eps)
    (Rk : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsKernel (Fm.ex x hx i)) (Cabs CH : ℝ) : Prop where
  pkg : DIVinN Fm → ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : Rk.1 ≤ x) (i : Fm.Ix x), Nonempty (DivisionPackageKernel (Rk.2 x hx h i) C Cabs)
  adm2 : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.LocalQuadraticParts.adm2 (Fm.D x i) (Fm.L x i)
  cut : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∀ μ, Formalism.BasicNotions.DV.Used (Fm.D x i) μ → Formalism.L2.G.ServJoint.CutUp (Fm.D x i) μ
  c3 : ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Compl3 (Fm.L x i) (Fm.X x i) Fm.Csz C
  hh : DIVinN Fm → Formalism.MainNotions.LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH
  c2 : Formalism.MainNotions.LocalQuadraticParts.ComplementTwoFamily Fm
  c5 : Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm
  bu : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational
  rr : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull
  la : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La

theorem BridgeRowsK.toT {eps : ℝ} {Fm : FamP eps}
    {Rk : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsKernel (Fm.ex x hx i)} {Cabs CH : ℝ}
    (B : BridgeRowsK Fm Rk Cabs CH) : BridgeRowsT Fm (rowsKtoT Rk) Cabs CH where
  pkg := fun hN => by
    obtain ⟨C, x0, h⟩ := B.pkg hN
    exact ⟨C, x0, fun x hx0 hx h' i => (h x hx0 hx h' i).map DivisionPackageKernel.toDivisionPackageColumns⟩
  adm2 := B.adm2
  cut := B.cut
  c3 := B.c3
  hh := B.hh
  c2 := B.c2
  c5 := B.c5
  bu := B.bu
  rr := B.rr
  la := B.la

theorem linkDIVt_of_rowsK {eps : ℝ} (Fm : FamP eps)
    (Rk : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsKernel (Fm.ex x hx i)) (Cabs CH : ℝ)
    (B : BridgeRowsK Fm Rk Cabs CH) : LinkDIVt Fm Cabs CH := by
  first
  | exact linkDIVt_of_rowsT Fm (rowsKtoT Rk) Cabs CH B.toT
  | exact linkDIVt_of_rowsT Fm _ Cabs CH B.toT
  | exact linkDIVt_of_rowsT B.toT
  | exact linkDIVt_of_T Fm (rowsKtoT Rk) Cabs CH B.toT
  | exact linkDIVt_of_bridgeT Fm (rowsKtoT Rk) Cabs CH B.toT
  | exact B.toT.link

theorem linkDIVt_closedK (𝒟 : FamClass) (Cabs : ℝ)
    (Rk : ∀ {eps : ℝ} (Fm : FamP eps), 𝒟 Fm →
      Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsKernel (Fm.ex x hx i))
    (h : Closed 𝒟 (fun Fm CH => ∀ hc : 𝒟 Fm, TuSize Fm → DGamSize Fm → BridgeRowsK Fm (Rk Fm hc) Cabs CH)) :
    Closed 𝒟 (fun Fm CH => TuSize Fm → DGamSize Fm → LinkDIVt Fm Cabs CH) := by
  obtain ⟨ε1, hε1, hK⟩ := h
  refine ⟨ε1, hε1, fun eps he he1 => ?_⟩
  obtain ⟨K, hKP⟩ := hK eps he he1
  exact ⟨K, fun Fm CH hc hL hT hG => linkDIVt_of_rowsK Fm (Rk Fm hc) Cabs CH (hKP Fm CH hc hL hc hT hG)⟩

end RowsK

end Formalism.L2.DIV

end
