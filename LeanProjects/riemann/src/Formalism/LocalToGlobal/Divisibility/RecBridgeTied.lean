import Mathlib
import Formalism.LocalToGlobal.Divisibility.LinkDIVL2R3Rec
import Formalism.LocalToGlobal.Divisibility.RecBridge
import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef

section FieldsLL

abbrev fieldsLL (D : Formalism.BasicNotions.D7) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL)) : Formalism.L2.Col.Fields :=
  { X with K := D.what₂.LL, fieldK := inferInstance, nfK := inferInstance, starK := inferInstance, emb := e }

theorem fieldsLL_K (D : Formalism.BasicNotions.D7) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL)) :
    (fieldsLL D X e).K = D.what₂.LL := rfl

end FieldsLL

section ColRec

open Formalism.BasicNotions Formalism.L2.Col

structure ColRec3 (X : Fields) {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
    (A3 : FamIn3 X.K G Pl0 I0 Ty T m) (P1 : Subgroup G) (ψ1 : P1 →* X.Kˣ) where
  Pr : Primes X
  Rk : Ranks
  W : Wts X Pr.Word Rk
  Ch : Chars X Pr Rk.m
  sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)
  Sg : Set ℕ
  hX : X.Ok
  Lv : LevFam X.E X.K Rk.r Pr.vGs
  Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs Rk.r → X.K)
  m2 : ℕ
  Gc : ChGlob X Rk.m
  mu : A3.fam3.base3.Tup → Tup X.F X.E X.K Sg
  cst : ∀ t, LocCst X (rowSG Pr sel (mu t))
  Li : ∀ t, ChIdx X Pr Rk (QE sel (mu t : Chr X.F X.E X.K))
  hL : ∀ t, (Li t).Ok Ch sel (mu t) (cst t) Gc m2
  hP : ∀ t, (mtildeGSD W Ch sel (mu t) Lv).Ok
  Mem : Type
  wd : Mem → Pr.Word
  b : ∀ t, Mem → (Li t).β (m2 + 1)
  hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (Li t) (wd x) m2 (b t x)
  Am : Formalism.L2.Ker.Amb X
  hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (Li t) Am (wd x) m2 (b t x) (hY t x) Lv
  hF : ∀ t x j, (chF W sel (mu t) (Li t) (wd x) j).Ok
  hE : ∀ x, (evGSD W Ch sel (mu A3.fam3.base3.μ0) Lv (wd x)).Ok
  ev : ∀ (Zs : DefSub A3.fam3.amb3) t, (Fin ((A3.side3 P1 ψ1 Zs).nV t) → X.K) →ₗ[X.K] V0X W Ch sel (mu t) Xg Lv

variable {X : Fields} {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 X.K G Pl0 I0 Ty T m} {P1 : Subgroup G} {ψ1 : P1 →* X.Kˣ}

abbrev ColRec3.ker (c : ColRec3 X A3 P1 ψ1) :
    ∀ t x, ChKer c.W c.Ch c.sel (c.mu t) (c.cst t) (c.Li t) c.Lv (c.wd x) c.m2 (c.b t x) (c.hY t x) :=
  kerRec c.mu c.cst c.Li c.wd c.b c.hY c.Am c.hK

abbrev ColRec3.face (c : ColRec3 X A3 P1 ψ1) (Zs : DefSub A3.fam3.amb3) : DefCols (A3.side3 P1 ψ1 Zs) :=
  colFace c.hX (A3.side3 P1 ψ1 Zs) c.Xg c.mu c.cst c.Li c.hL c.hP c.Mem c.wd c.b c.hY c.ker c.hF (c.ev Zs)

abbrev ColRec3.memQ (c : ColRec3 X A3 P1 ψ1) (x : c.Mem) : KerChain X.K :=
  Formalism.L2.DIV.memQ (A := c.ker) (hF := c.hF) c.hE (x := x)

theorem ColRec3.face_pt (c : ColRec3 X A3 P1 ψ1) (Zs : DefSub A3.fam3.amb3) (x : c.Mem) (t : A3.fam3.base3.Tup) :
    (c.face Zs).Pt x t = colPer c.hX (c.hP t) c.Xg (c.ker t x) (c.hF t x) (c.hL t) (c.ev Zs t) := rfl

end ColRec

section Rows

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions

variable {D : D7}

def DivisionRowsFace.ofCol3 (L : SizeData₂ D) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL)) {G : Type} [Group G] [Fintype G]
    {Pl0 I0 Ty T : Type} (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ)
    (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ) (c : ColRec3 (fieldsLL D X e) A3 P1 ψ1)
    (Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (c.face Zs)) (Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3)
    (Zs : DefSub A3.fam3.amb3) (stable : Zs.Stable) (inBlock : Zs.InBlock) {s : ℕ} (hOk : A3.fam3.Ok3 s)
    (hsep : A3.fam3.TypesSep3) (what₂ : IndefRows (A3.side3 P0 ψ0 Zs)) : DivisionRowsFace L where
  Bs := A3.fam3.base3
  Am := A3.fam3.amb3
  fc := Formalism.IndefR.Cx.faceOf3 A3 P0 ψ0 P1 ψ1 c.face Sp Zsc
  Zs := Zs
  stable := stable
  inBlock := inBlock
  wf0 := A3.side_well_formed hOk P0 ψ0 Zs stable inBlock hsep
  wf1 := A3.side_well_formed hOk P1 ψ1 Zs stable inBlock hsep
  what₂ := what₂

structure DivisionRowsColumns (L : SizeData₂ D) where
  X : Formalism.L2.Col.Fields
  e : X.Tau → (X.E →+* D.what₂.LL)
  G : Type
  [grp : Group G]
  [fin : Fintype G]
  Pl0 : Type
  I0 : Type
  Ty : Type
  T : Type
  A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T D.R.m
  P0 : Subgroup G
  ψ0 : P0 →* D.what₂.LLˣ
  P1 : Subgroup G
  ψ1 : P1 →* D.what₂.LLˣ
  c : ColRec3 (fieldsLL D X e) A3 P1 ψ1
  Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (c.face Zs)
  Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3
  Zs : DefSub A3.fam3.amb3
  stable : Zs.Stable
  inBlock : Zs.InBlock
  s : ℕ
  hOk : A3.fam3.Ok3 s
  hsep : A3.fam3.TypesSep3
  what₂ : IndefRows (A3.side3 P0 ψ0 Zs)

attribute [instance] DivisionRowsColumns.grp DivisionRowsColumns.fin

abbrev DivisionRowsColumns.toF {L : SizeData₂ D} (R : DivisionRowsColumns L) : DivisionRowsFace L :=
  DivisionRowsFace.ofCol3 L R.X R.e R.A3 R.P0 R.ψ0 R.P1 R.ψ1 R.c R.Sp R.Zsc R.Zs R.stable R.inBlock R.hOk R.hsep R.what₂

theorem DivisionRowsColumns.toF_Dc {L : SizeData₂ D} (R : DivisionRowsColumns L) (Zs : DefSub R.A3.fam3.amb3) : (R.toF.fc Zs).Dc = R.c.face Zs := rfl

structure DivisionPackageColumns {L : SizeData₂ D} (Rt : DivisionRowsColumns L) (C Cabs : ℝ) extends DivisionPackageFace Rt.toF C Cabs where
  hQ : ∀ u, ChainTie (inp u).ch (Rt.c.memQ (wU u))
  h0 : ∀ u, FirstCols Rt.c.hE (hQ u)

theorem DivisionPackageColumns.wordFacts {L : SizeData₂ D} {Rt : DivisionRowsColumns L} {C Cabs : ℝ} (P : DivisionPackageColumns Rt C Cabs)
    (h2 : Formalism.MainNotions.LocalQuadraticParts.adm2 D L) (hcut : ∀ μ, Formalism.BasicNotions.DV.Used D μ → Formalism.L2.G.ServJoint.CutUp D μ)
    (hN : Formalism.BasicNotions.DV.NprimeDef D L) (u : D.what₂.Word) : WordFacts L C Cabs u :=
  DivisionPackageFace.wordFacts P.toDivisionPackageFace h2 hcut hN u

def DivisionPackageColumns.inputs {L : SizeData₂ D} {Rt : DivisionRowsColumns L} {C Cabs : ℝ} (P : DivisionPackageColumns Rt C Cabs)
    (h2 : Formalism.MainNotions.LocalQuadraticParts.adm2 D L) (hcut : ∀ μ, Formalism.BasicNotions.DV.Used D μ → Formalism.L2.G.ServJoint.CutUp D μ)
    (hN : Formalism.BasicNotions.DV.NprimeDef D L) (u : D.what₂.Word) : DivInputsR P.Pk.core (P.R u) (P.wU u) (P.Nu u) (sgRec L u) :=
  { toDivInputs0R := P.inp u,
    val2 := Formalism.L2.G.ServJointF.val2AllAtRF D L _ P.brTied hcut h2 u (P.Nu u)
      (Formalism.L2.G.ServJoint.nu_into L hN u (P.eNu u) (P.NuC (P.wU u)) (P.Nu u) (P.hNu u).lat (P.shift u)) }

theorem DivisionPackageColumns.linkRec {L : SizeData₂ D} {Rt : DivisionRowsColumns L} {C Cabs : ℝ} (P : DivisionPackageColumns Rt C Cabs)
    (h2 : Formalism.MainNotions.LocalQuadraticParts.adm2 D L) (hcut : ∀ μ, Formalism.BasicNotions.DV.Used D μ → Formalism.L2.G.ServJoint.CutUp D μ)
    (hN : Formalism.BasicNotions.DV.NprimeDef D L) (u : D.what₂.Word) :
    DivClausesR P.Pk.core (P.R u) (P.wU u) (P.Nu u) (sgRec L u) ∧
      (∀ y : Fin ((P.inp u).ch.c 0) → D.what₂.LL,
        (P.hQ u).coL ((chainMat (P.inp u).ch.Kj ⟨(Rt.c.memQ (P.wU u)).n + 1, by have := (P.hQ u).hmm; omega⟩).mulVec y) =
          Formalism.L2.Ker.colMu Rt.c.W Rt.c.Ch Rt.c.sel (Rt.c.mu Rt.A3.fam3.base3.μ0) (Rt.c.cst Rt.A3.fam3.base3.μ0) (Rt.c.Li Rt.A3.fam3.base3.μ0)
            Rt.c.Am (Rt.c.wd (P.wU u)) Rt.c.m2 (Rt.c.b Rt.A3.fam3.base3.μ0 (P.wU u)) (Rt.c.hY Rt.A3.fam3.base3.μ0 (P.wU u)) Rt.c.Lv
            (Rt.c.hK Rt.A3.fam3.base3.μ0 (P.wU u)) (Rt.c.hF Rt.A3.fam3.base3.μ0 (P.wU u)) (Rt.c.hL Rt.A3.fam3.base3.μ0)
            (colOfCoord Rt.c.W Rt.c.Ch Rt.c.hX (Rt.c.wd (P.wU u)) fun i => y (Fin.cast (P.inp u).ch.c0.symm i))) ∧
      ∀ (φ : Fin (ramDim Rt.c.W Rt.c.Ch Rt.c.hX (Rt.c.wd (P.wU u))) → D.what₂.LL)
        (F : Fin ((Rt.A3.side3 Rt.P1 Rt.ψ1 P.Pk.Zs).nV Rt.A3.fam3.base3.μ0) → D.what₂.LL),
        (P.inp u).ch.PtL ((chainMat (P.inp u).ch.Kj (Fin.last (P.inp u).ch.mm)).mulVec fun i => φ (Fin.cast (P.inp u).ch.c0 i)) F =
          colPerL (Rt.c.hP Rt.A3.fam3.base3.μ0) Rt.c.Xg (Rt.c.wd (P.wU u)) (Rt.c.ev P.Pk.Zs Rt.A3.fam3.base3.μ0)
            (Formalism.L2.Ker.colMu Rt.c.W Rt.c.Ch Rt.c.sel (Rt.c.mu Rt.A3.fam3.base3.μ0) (Rt.c.cst Rt.A3.fam3.base3.μ0) (Rt.c.Li Rt.A3.fam3.base3.μ0)
              Rt.c.Am (Rt.c.wd (P.wU u)) Rt.c.m2 (Rt.c.b Rt.A3.fam3.base3.μ0 (P.wU u)) (Rt.c.hY Rt.A3.fam3.base3.μ0 (P.wU u)) Rt.c.Lv
              (Rt.c.hK Rt.A3.fam3.base3.μ0 (P.wU u)) (Rt.c.hF Rt.A3.fam3.base3.μ0 (P.wU u)) (Rt.c.hL Rt.A3.fam3.base3.μ0)
              (colOfCoord Rt.c.W Rt.c.Ch Rt.c.hX (Rt.c.wd (P.wU u)) φ)) F := by
  exact linkDIV_L2R3_rec (X := fieldsLL D Rt.X Rt.e) Rt.A3 Rt.hOk Rt.hsep Rt.P0 Rt.ψ0 Rt.P1 Rt.ψ1 Rt.c.hX Rt.c.Xg
    Rt.c.mu Rt.c.cst Rt.c.Li Rt.c.hL Rt.c.hP Rt.c.Mem Rt.c.wd Rt.c.b Rt.c.hY Rt.c.Am Rt.c.hK Rt.c.hF Rt.c.hE Rt.c.ev
    Rt.Sp Rt.Zsc P.cf P.Cp P.CHp P.Pk (P.R u) (P.wU u) (P.Nu u) (sgRec L u) (P.inputs h2 hcut hN u) (P.hQ u) (P.h0 u)

structure BridgeRowsT {eps : ℝ} (Fm : FamP eps) (Rt : Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsColumns (Fm.L x i))
    (Cabs CH : ℝ) : Prop where
  pkg : DIVinN Fm → ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : Rt.1 ≤ x) (i : Fm.Ix x), Nonempty (DivisionPackageColumns (Rt.2 x hx h i) C Cabs)
  adm2 : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.MainNotions.LocalQuadraticParts.adm2 (Fm.D x i) (Fm.L x i)
  cut : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∀ μ, Formalism.BasicNotions.DV.Used (Fm.D x i) μ → Formalism.L2.G.ServJoint.CutUp (Fm.D x i) μ
  c3 : ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Compl3 (Fm.L x i) (Fm.X x i) Fm.Csz C
  hh : DIVinN Fm → Formalism.MainNotions.LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH
  c2 : Formalism.MainNotions.LocalQuadraticParts.ComplementTwoFamily Fm
  c5 : Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm
  bu : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational
  rr : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull
  la : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La

abbrev rowsTtoF {eps : ℝ} {Fm : FamP eps} (Rt : Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsColumns (Fm.L x i)) :
    Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsFace (Fm.L x i) :=
  ⟨Rt.1, fun x hx h i => (Rt.2 x hx h i).toF⟩

theorem BridgeRowsT.toF {eps : ℝ} {Fm : FamP eps} {Rt : Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsColumns (Fm.L x i)}
    {Cabs CH : ℝ} (B : BridgeRowsT Fm Rt Cabs CH) : BridgeRowsF Fm (rowsTtoF Rt) Cabs CH where
  pkg := fun hN => by
    obtain ⟨C, x0, h⟩ := B.pkg hN
    exact ⟨C, x0, fun x hx0 hx h' i => (h x hx0 hx h' i).map DivisionPackageColumns.toDivisionPackageFace⟩
  adm2 := B.adm2
  cut := B.cut
  c3 := B.c3
  hh := B.hh
  c2 := B.c2
  c5 := B.c5
  bu := B.bu
  rr := B.rr
  la := B.la

theorem linkDIVt_of_rowsT {eps : ℝ} (Fm : FamP eps)
    (Rt : Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsColumns (Fm.L x i)) (Cabs CH : ℝ)
    (B : BridgeRowsT Fm Rt Cabs CH) : LinkDIVt Fm Cabs CH :=
  linkDIVt_of_rowsF Fm (rowsTtoF Rt) Cabs CH B.toF

theorem linkDIVt_closedT (𝒟 : FamClass) (Cabs : ℝ)
    (Rt : ∀ {eps : ℝ} (Fm : FamP eps), 𝒟 Fm → Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsColumns (Fm.L x i))
    (h : Closed 𝒟 (fun Fm CH => ∀ hc : 𝒟 Fm, TuSize Fm → DGamSize Fm → BridgeRowsT Fm (Rt Fm hc) Cabs CH)) :
    Closed 𝒟 (fun Fm CH => TuSize Fm → DGamSize Fm → LinkDIVt Fm Cabs CH) := by
  refine linkDIVt_closedF 𝒟 Cabs (fun Fm hc => rowsTtoF (Rt Fm hc)) ?_
  obtain ⟨ε1, hε1, hK⟩ := h
  refine ⟨ε1, hε1, fun eps he hle => ?_⟩
  obtain ⟨K, hK'⟩ := hK eps he hle
  exact ⟨K, fun Fm CH hD hL hc hT hG => (hK' Fm CH hD hL hc hT hG).toF⟩

end Rows

section IndefiniteRowSideFullHecke

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Rows

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

def ColTie3 (P : RowSideFamily ex) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL)) (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs)
    (Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)) : Prop :=
  c.face P.Zs = P.Dc ∧ HEq (Sp P.Zs) P.Sp

def DivisionRowsColumns.split_model_to_place_model (P : RowSideFamily ex) (hr : RowsHold0_3 P) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL))
    (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs) (Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs))
    (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) : DivisionRowsColumns L where
  X := X
  e := e
  G := P.Gp
  Pl0 := P.Pl0
  I0 := P.I0
  Ty := List ℕ
  T := P.T
  A3 := P.A3
  P0 := P.P0
  ψ0 := P.ψ0
  P1 := P.Ps
  ψ1 := P.ψs
  c := c
  Sp := Sp
  Zsc := Zsc
  Zs := P.Zs
  stable := hr.zsSt
  inBlock := hr.zsBl
  s := Classical.choose hr.famOk
  hOk := Classical.choose_spec hr.famOk
  hsep := hr.famSep
  what₂ := Classical.choose hr.rows0

theorem DivisionRowsColumns.of_tied_subspaces_eq (P : RowSideFamily ex) (hr : RowsHold0_3 P) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL))
    (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs) (Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs))
    (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) : (DivisionRowsColumns.split_model_to_place_model (L := L) P hr X e c Sp Zsc).toF.Zs = P.Zs := rfl

theorem DivisionRowsColumns.of_tied_rows_eq (P : RowSideFamily ex) (hr : RowsHold0_3 P) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL))
    (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs) (Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs))
    (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) :
    (DivisionRowsColumns.split_model_to_place_model (L := L) P hr X e c Sp Zsc).toF.what₂.toIndefData = P.S0 :=
  Classical.choose_spec hr.rows0

theorem DivisionRowsColumns.of_tied_columns_eq (P : RowSideFamily ex) (hr : RowsHold0_3 P) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL))
    (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs) (Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs))
    (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (h : ColTie3 P X e c Sp) :
    ((DivisionRowsColumns.split_model_to_place_model (L := L) P hr X e c Sp Zsc).toF.fc P.Zs).Dc = P.Dc ∧
      HEq ((DivisionRowsColumns.split_model_to_place_model (L := L) P hr X e c Sp Zsc).toF.fc P.Zs).Sp P.Sp :=
  ⟨h.1, h.2⟩

def EvTie3 (P : RowSideFamily ex) (hr : RowsHold0_3 P) (X : Formalism.L2.Col.Fields) (e : X.Tau → (X.E →+* D.what₂.LL))
    (c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs) (Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs))
    (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) {C Cabs : ℝ}
    (Pt : DivisionPackageColumns (DivisionRowsColumns.split_model_to_place_model (L := L) P hr X e c Sp Zsc) C Cabs) : Prop :=
  (∀ t, Pt.tup t = P.I.tup t) ∧
    ∀ t (F : Fin ((P.A3.side3 P.Ps P.ψs Pt.Pk.Zs).nV t) → D.what₂.LL),
      HEq (Pt.eV t F) (P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))

theorem EvTie3.pin {P : RowSideFamily ex} {hr : RowsHold0_3 P} {X : Formalism.L2.Col.Fields} {e : X.Tau → (X.E →+* D.what₂.LL)}
    {c : ColRec3 (fieldsLL D X e) P.A3 P.Ps P.ψs} {Sp : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (c.face Zs)}
    {Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {C Cabs : ℝ}
    {Pt : DivisionPackageColumns (DivisionRowsColumns.split_model_to_place_model (L := L) P hr X e c Sp Zsc) C Cabs} (h : EvTie3 P hr X e c Sp Zsc Pt)
    (u : D.what₂.Word) (t : P.A3.fam3.base3.Tup) (x : Fin (ramDim c.W c.Ch c.hX (c.wd (Pt.wU u))) → D.what₂.LL)
    (F : Fin ((P.A3.side3 P.Ps P.ψs Pt.Pk.Zs).nV t) → D.what₂.LL) :
    D.what₂.embLL (colPer c.hX (c.hP t) c.Xg (c.ker t (Pt.wU u)) (c.hF t (Pt.wU u)) (c.hL t) (c.ev Pt.Pk.Zs t) x F) =
      D.what₂.perCol u (P.I.tup t) (D.jN u (Pt.eNu u x)) (P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F)) := by
  have key : ∀ (a b : D.what₂.Tup) (hab : a = b) (va : D.what₂.Amb a) (vb : D.what₂.Amb b), HEq va vb →
      D.what₂.perCol u a (D.jN u (Pt.eNu u x)) va = D.what₂.perCol u b (D.jN u (Pt.eNu u x)) vb := by
    intro a b hab va vb hv
    subst hab
    rw [eq_of_heq hv]
  exact (Pt.brTied.dcPt u t x F).trans (key _ _ (h.1 t) _ _ (h.2 t F))

end IndefiniteRowSideFullHecke

end Formalism.L2.DIV

end
