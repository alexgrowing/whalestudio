import Mathlib
import Formalism.LocalToGlobal.Divisibility.ColPins
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV.Member

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.L2.Rows Formalism.L2.Col Formalism.L2.DIV

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

section Fam

variable {X : Fields} {e : X.Tau → (X.E →+* D.what₂.LL)} {Pr : Primes (fieldsLL D X e)}
  (W : Wts (fieldsLL D X e) Pr.Word D.R) (Ch : Chars (fieldsLL D X e) Pr D.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (hX : (fieldsLL D X e).Ok)
  (v0 : InfinitePlace D.what₂.LL) (TU : Finset (Tup X.F X.E D.what₂.LL Sg))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs D.R.r → D.what₂.LL))
  (xiVal : Tup X.F X.E D.what₂.LL Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ)
  (trIv : Fin D.R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL)

abbrev famM : FamIn3 D.what₂.LL (Formalism.L2.Col.G0 X.E Pr.vGs D.R.r) (Formalism.L2.Col.LevOff ∅ Pr.vGs ∅)
    (Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅) (List ℕ) (TupF (X := fieldsLL D X e) TU) D.R.m :=
  colIn3 W Ch sel hX v0 TU Xg ∅ xiVal trIv

end Fam

section Cols

section Gen

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (Gc : ChGlob X R.m) (m2 : ℕ) (Mem : Type)

structure ColFam : Type 1 where
  cst : ∀ μ : Tup X.F X.E X.K Sg, LocCst X (rowSG Pr sel μ)
  Li : ∀ μ : Tup X.F X.E X.K Sg, ChIdx X Pr R (QE sel (μ : Chr X.F X.E X.K))
  hL : ∀ μ : Tup X.F X.E X.K Sg, (Li μ).Ok Ch sel μ (cst μ) Gc m2
  hP : ∀ μ : Tup X.F X.E X.K Sg, (mtildeGSD W Ch sel μ (rPsymF (R := R) Ch)).Ok
  wd : Mem → Pr.Word
  b : ∀ μ : Tup X.F X.E X.K Sg, Mem → (Li μ).β (m2 + 1)
  hY : ∀ (μ : Tup X.F X.E X.K Sg) (x : Mem), YbHyp (R := R) sel μ (cst μ) (Li μ) (wd x) m2 (b μ x)
  Am : Formalism.L2.Ker.Amb X
  hK : ∀ (μ : Tup X.F X.E X.K Sg) (x : Mem),
    Formalism.L2.Ker.KerEquivC W Ch sel μ (cst μ) (Li μ) Am (wd x) m2 (b μ x) (hY μ x) (rPsymF (R := R) Ch)
  hF : ∀ (μ : Tup X.F X.E X.K Sg) (x : Mem) j, (chF W sel μ (Li μ) (wd x) j).Ok

end Gen

variable {X : Fields} {e : X.Tau → (X.E →+* D.what₂.LL)} {Pr : Primes (fieldsLL D X e)}
  (W : Wts (fieldsLL D X e) Pr.Word D.R) (Ch : Chars (fieldsLL D X e) Pr D.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} (Gc : ChGlob (fieldsLL D X e) D.R.m) (m2 : ℕ)

open Classical in

def psiM : ∀ PP : Pl X.E, AddChar (kP PP) D.what₂.LL :=
  fun PP => if h : PP ∈ Pr.vGs then Ch.psi0 ⟨PP, h⟩ else 1

variable {W Ch sel Gc m2} (F : ColFam W Ch sel Sg Gc m2 D.what₂.Word) (hX : (fieldsLL D X e).Ok)
  (v0 : InfinitePlace D.what₂.LL) (TU : Finset (Tup X.F X.E D.what₂.LL Sg))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs D.R.r → D.what₂.LL))
  (xiVal : Tup X.F X.E D.what₂.LL Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ)
  (trIv : Fin D.R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL)

def colM
    (hE : ∀ x, (evGSD W Ch sel ((famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.base3.μ0 : TupF (X := fieldsLL D X e) TU).1
      (rPsymF (R := D.R) Ch) (F.wd x)).Ok)
    (ev : ∀ (Zs : DefSub (famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.amb3) (t : TupF (X := fieldsLL D X e) TU),
      (Fin (((famM W Ch sel hX v0 TU Xg xiVal trIv).side3 (rPsymF (R := D.R) Ch).grp (rPsymF (R := D.R) Ch).chr Zs).nV t) →
        D.what₂.LL) →ₗ[D.what₂.LL] V0X W Ch sel t.1 Xg (rPsymF (R := D.R) Ch)) :
    ColRec3 (fieldsLL D X e) (famM W Ch sel hX v0 TU Xg xiVal trIv) (rPsymF (R := D.R) Ch).grp (rPsymF (R := D.R) Ch).chr where
  Pr := Pr
  Rk := D.R
  W := W
  Ch := Ch
  sel := sel
  Sg := Sg
  hX := hX
  Lv := rPsymF (R := D.R) Ch
  Xg := Xg
  m2 := m2
  Gc := Gc
  mu := fun t => t.1
  cst := fun t => F.cst t.1
  Li := fun t => F.Li t.1
  hL := fun t => F.hL t.1
  hP := fun t => F.hP t.1
  Mem := D.what₂.Word
  wd := F.wd
  b := fun t => F.b t.1
  hY := fun t => F.hY t.1
  Am := F.Am
  hK := fun t => F.hK t.1
  hF := fun t => F.hF t.1
  hE := hE
  ev := ev

end Cols

section IndefiniteRowSideFullHecke

structure ExtendedDataRemainder {G Pl0 I0 Tt : Type} [Group G] [Fintype G] (ex : Extra D L hT Gi Gl Kc Y cX)
    (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) Tt D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* D.what₂.LLˣ) (Dcf : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs))
    (Spf : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dcf Zs)) : Type 1 where
  Zs : DefSub A3.fam3.amb3
  S0 : IndefData (A3.side3 P0 ψ0 Zs)
  S1 : IndefData (A3.side3 P1 ψ1 Zs)
  C : ColData (Dcf Zs) (Spf Zs) S1
  NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin ((Dcf Zs).a u) → D.what₂.LL)
  I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 P1 ψ1 Zs S0 S1 ex.p0 (Dcf Zs)
  JA : AmbIds D A3.A ex.p0.s ex.amb0 P0 ψ0 I.tup
  JM : MjHIds D A3.A Y (A3.indefDown S0)
  tied : BaseDivisionAmbientCompatibilityFamily D A3 Y ex.p0 ex.amb0 P0 ψ0 P1 ψ1 Zs S0 S1 C NuC I JA JM

variable {G Pl0 I0 Tt : Type} [Group G] [Fintype G] {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) Tt D.R.m} {P0 : Subgroup G}
  {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ} {Dcf : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Spf : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dcf Zs)}

def ExtendedDataRemainder.extendedDatum (R : ExtendedDataRemainder ex A3 P0 ψ0 P1 ψ1 Dcf Spf) : RowSideFamily ex :=
  ⟨G, Pl0, I0, Tt, A3, P0, ψ0, P1, ψ1, R.Zs, R.S0, R.S1, Dcf R.Zs, Spf R.Zs, R.C, R.NuC, R.I, R.JA, R.JM, R.tied⟩

end IndefiniteRowSideFullHecke

section K

variable {X : Fields} {e : X.Tau → (X.E →+* D.what₂.LL)} {Pr : Primes (fieldsLL D X e)}
  {W : Wts (fieldsLL D X e) Pr.Word D.R} {Ch : Chars (fieldsLL D X e) Pr D.R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ} {Gc : ChGlob (fieldsLL D X e) D.R.m} {m2 : ℕ}
  (F : ColFam W Ch sel Sg Gc m2 D.what₂.Word) (hX : (fieldsLL D X e).Ok)
  (v0 : InfinitePlace D.what₂.LL) (TU : Finset (Tup X.F X.E D.what₂.LL Sg))
  (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs D.R.r → D.what₂.LL))
  (xiVal : Tup X.F X.E D.what₂.LL Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ)
  (trIv : Fin D.R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL)
  (hE : ∀ x, (evGSD W Ch sel ((famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.base3.μ0 : TupF (X := fieldsLL D X e) TU).1
      (rPsymF (R := D.R) Ch) (F.wd x)).Ok)
  (ev : ∀ (Zs : DefSub (famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.amb3) (t : TupF (X := fieldsLL D X e) TU),
      (Fin (((famM W Ch sel hX v0 TU Xg xiVal trIv).side3 (rPsymF (R := D.R) Ch).grp (rPsymF (R := D.R) Ch).chr Zs).nV t) →
        D.what₂.LL) →ₗ[D.what₂.LL] V0X W Ch sel t.1 Xg (rPsymF (R := D.R) Ch))
  (Sp : ∀ Zs, SPer ((colM F hX v0 TU Xg xiVal trIv hE ev).face Zs))

abbrev RestM (ex : Extra D L hT Gi Gl Kc Y cX) :=
  ExtendedDataRemainder ex (famM W Ch sel hX v0 TU Xg xiVal trIv) (Formalism.L2.DIV.P0 Pr.vGs D.R.r (psiM Ch)).H
    (Formalism.L2.DIV.P0 Pr.vGs D.R.r (psiM Ch)).chi (rPsymF (R := D.R) Ch).grp (rPsymF (R := D.R) Ch).chr
    (colM F hX v0 TU Xg xiVal trIv hE ev).face Sp

variable {F hX v0 TU Xg xiVal trIv hE ev Sp} (T : TiedDataSK ex) (R : RestM F hX v0 TU Xg xiVal trIv hE ev Sp ex)

def colK (hKer : ColTieT T R.extendedDatum X e (colM F hX v0 TU Xg xiVal trIv hE ev)) (hwU : ∀ u, HEq (R.I.wU u) u)
    (hsg : F.Am.σ₀ = D.what₂.embLL) (hH : ColHyp3 W Ch sel v0 TU Xg ∅) : SquareIntegrableColumnsCompatible T R.extendedDatum where
  X := X
  e := e
  c := colM F hX v0 TU Xg xiVal trIv hE ev
  Sp := Sp
  colTie := ⟨rfl, HEq.rfl⟩
  kerTie := hKer
  wTie := hwU
  lvTie := rfl
  sgTie := hsg
  v0 := v0
  TU := TU
  xiVal := xiVal
  trIv := trIv
  famEq := HEq.rfl
  gEq := rfl
  plEq := rfl
  i0Eq := rfl
  tEq := rfl
  muTie := fun _ => rfl
  ok1 := colFam3_ok W Ch sel hX v0 TU Xg ∅ xiVal trIv hH

theorem kerTieM (hXk : T.ker.X = fieldsLL D X e) (hPr : HEq Pr T.ker.Pr) (hCh : HEq Ch T.ker.Ch) (hsl : HEq sel T.ker.sel)
    (hSg : HEq Sg T.ker.S)
    (hmu : HEq (fun t : TupF (X := fieldsLL D X e) TU => t.1) (fun t : TupF (X := fieldsLL D X e) TU => T.ker.tup (R.I.tup t)))
    (hcst : HEq (fun t : TupF (X := fieldsLL D X e) TU => F.cst t.1) (fun t : TupF (X := fieldsLL D X e) TU => T.ker.cst (R.I.tup t)))
    (hLi : HEq (fun t : TupF (X := fieldsLL D X e) TU => F.Li t.1) (fun t : TupF (X := fieldsLL D X e) TU => T.ker.idx (R.I.tup t)))
    (hm2 : m2 = T.ker.m2) (hGc : HEq Gc T.ker.glob)
    (hAm : HEq F.Am (Formalism.L2.Ker.ambOf T.ker.seam T.ker.B T.ker.χ T.ker.cD)) (hwd : HEq F.wd T.ker.word) :
    ColTieT T R.extendedDatum X e (colM F hX v0 TU Xg xiVal trIv hE ev) :=
  ⟨hXk, rfl, hPr, hCh, hsl, hSg, hmu, hcst, hLi, hm2, hGc, hAm, rfl, hwd⟩

end K

section Pins

variable {T : TiedDataSK ex} {P : RowSideFamily ex}

open Classical in

structure PinRows (K : SquareIntegrableColumnsCompatible T P) : Prop where

  hcTie : ∀ (u : D.what₂.Word) (τ : D.what₂.Tau),
    HEq (K.c.W.hc (K.c.wd (cast K.kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1.symm u))
      (cast (congrArg Formalism.L2.Col.Fields.Tau K.kerTie.1) (T.ker.seam.iT.symm τ))) (D.hcW u τ)

  wtTie : ∃ (sh : D.what₂.Word → ℕ → D.what₂.Tau → ℤ) (n : D.what₂.Word → ℕ → D.what₂.Tau → ℕ),
    Formalism.L2.Ker.KerEntTied.WtTie T.ker (lamOfCol K) sh n

  xgTie : ∀ χ : Formalism.L2.Col.G0 K.X.E K.c.Pr.vGs K.c.Rk.r → D.what₂.LL,
    χ ∈ K.c.Xg ↔ (fun g => χ (cast K.gEq (P.I.eG.symm g))) ∈ Formalism.L2.Col.XgE K.c.Am.σ₀ D.ntypes.e0

  qNF : ∀ (t : P.A3.fam3.base3.Tup) (j : ℕ) (b : (K.c.Li t).β j)
      (v : ↥(Formalism.L2.Col.uSG K.c.Pr.vGs (Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL)))),
      v.1 ∉ K.c.Pr.vGs → 1 ≤ j → j + 2 ≤ K.c.Rk.m →
      ∃ (nn : Fin (Formalism.L2.Col.cOf K.c.Rk j) → ℤ) (z : Fin (K.c.Rk.N j) → K.X.E),
        (∀ i, -(j : ℤ) ≤ nn i ∧ nn i ≤ 0) ∧
        (fun l : Fin (K.c.Rk.N j + Formalism.L2.Col.cOf K.c.Rk j) => if h : l.1 < K.c.Rk.N j then z ⟨l.1, h⟩ else 0) ∈
          Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1 ∧
        (Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1).map
                  (((K.c.Li t).h j b v).toLinearMap.restrictScalars (𝓞 K.X.E)) =
          (Formalism.L2.Col.lamYat (Pr := K.c.Pr) (R := K.c.Rk) j v.1).map
            ((Matrix.toLin' (nfMat (K.c.Rk.N j) (Formalism.L2.Col.cOf K.c.Rk j) ((Formalism.L2.Col.qOf v.1 : ℕ) : K.X.E) nn z)).restrictScalars
              (𝓞 K.X.E))

  columnEvaluationOk : ∃ hM : (Formalism.L2.Col.rowGSD K.c.W (Formalism.L2.Col.rowTyG K.c.Ch K.c.Lv).inv).Ok, ∀ u : D.what₂.Word,
    ∃ ι : (D.mem u).P.Mt ≃ₗ[ℂ] (Fin ((Formalism.L2.Col.rowGSD K.c.W (Formalism.L2.Col.rowTyG K.c.Ch K.c.Lv).inv).hDim hM) → ℂ),
      (∀ (t : P.A3.fam3.base3.Tup) (ht : P.I.tup t = D.what₂.mu0)
        (hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL) = ∅)
        (y : Fin (rDim D P.A3.A P.Ps P.ψs t) → D.what₂.LL),
        ∃ (F' : (Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).EqFun)
          (hm : F'.1 ∈ (Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Lv).EqFun),
          HEq ((Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).res
              (Formalism.L2.Col.mtildeKOk K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.hX) F')
            ((P.A3.A.fam.R t).S.basis.equivFun.symm
              (((P.A3.A.fam.R t).S.cutE (P.A3.A.fam.R t).r (lvlIdem (P.A3.A.fam.lvl P.Ps P.ψs).P
                (P.A3.A.fam.lvl P.Ps P.ψs).ψ)).mulVec y)) ∧
          ι ((D.eMt u).symm (ht ▸ P.I.jA t y)) =
            Formalism.L2.Col.zOfRow K.c.W K.c.Ch K.c.sel (K.c.mu t) hQ K.c.Lv K.c.Am.σ₀ hM ⟨F'.1, hm⟩) ∧
      ∀ (t : P.A3.fam3.base3.Tup) (ht : P.I.tup t = D.what₂.mu0)
        (hQ : Formalism.L2.Col.QE K.c.sel (K.c.mu t : Chr K.X.F K.X.E D.what₂.LL) = ∅)
        (F : Fin ((P.A3.side3 P.Ps P.ψs P.Zs).nV t) → D.what₂.LL),
        ∃ hm : ((K.c.ev P.Zs t F : Formalism.L2.Col.V0X K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Xg K.c.Lv) :
            (Formalism.L2.Col.mtildeKGSD K.c.W K.c.Ch K.c.sel (K.c.mu t)).EqFun).1 ∈
            (Formalism.L2.Col.mtildeGSD K.c.W K.c.Ch K.c.sel (K.c.mu t) K.c.Lv).EqFun,
          ι ((D.eMt u).symm (ht ▸ P.I.jA t ((rV0 D P.A3.A P.Ps P.ψs t).mulVec F))) =
            Formalism.L2.Col.zOfRow K.c.W K.c.Ch K.c.sel (K.c.mu t) hQ K.c.Lv K.c.Am.σ₀ hM ⟨_, hm⟩

variable {X : Fields} {e : X.Tau → (X.E →+* D.what₂.LL)} {Pr : Primes (fieldsLL D X e)}
  {W : Wts (fieldsLL D X e) Pr.Word D.R} {Ch : Chars (fieldsLL D X e) Pr D.R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {Sg : Set ℕ} {Gc : ChGlob (fieldsLL D X e) D.R.m} {m2 : ℕ}
  {F : ColFam W Ch sel Sg Gc m2 D.what₂.Word} {hX : (fieldsLL D X e).Ok}
  {v0 : InfinitePlace D.what₂.LL} {TU : Finset (Tup X.F X.E D.what₂.LL Sg)}
  {Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs D.R.r → D.what₂.LL)}
  {xiVal : Tup X.F X.E D.what₂.LL Sg → HeightOneSpectrum (𝓞 X.E) → D.what₂.LLˣ}
  {trIv : Fin D.R.m → (Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL) →
    Formalism.L2.Col.LevOffI ∅ Pr.vGs ∅ × List ℕ → D.what₂.LL}
  {hE : ∀ x, (evGSD W Ch sel ((famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.base3.μ0 : TupF (X := fieldsLL D X e) TU).1
      (rPsymF (R := D.R) Ch) (F.wd x)).Ok}
  {ev : ∀ (Zs : DefSub (famM W Ch sel hX v0 TU Xg xiVal trIv).fam3.amb3) (t : TupF (X := fieldsLL D X e) TU),
      (Fin (((famM W Ch sel hX v0 TU Xg xiVal trIv).side3 (rPsymF (R := D.R) Ch).grp (rPsymF (R := D.R) Ch).chr Zs).nV t) →
        D.what₂.LL) →ₗ[D.what₂.LL] V0X W Ch sel t.1 Xg (rPsymF (R := D.R) Ch)}
  {Sp : ∀ Zs, SPer ((colM F hX v0 TU Xg xiVal trIv hE ev).face Zs)}
  {R : RestM F hX v0 TU Xg xiVal trIv hE ev Sp ex}
  {hKer : ColTieT T R.extendedDatum X e (colM F hX v0 TU Xg xiVal trIv hE ev)} {hwU : ∀ u, HEq (R.I.wU u) u}
  {hsg : F.Am.σ₀ = D.what₂.embLL} {hH : ColHyp3 W Ch sel v0 TU Xg ∅}

theorem colPinsM (hW : W.Ok) (hCh : Ch.Ok) (hr : PinRows (colK T R hKer hwU hsg hH)) : ColPins (colK T R hKer hwU hsg hH) where
  grpTie := HEq.rfl
  psTie := ⟨HEq.rfl, HEq.rfl⟩
  pointCharacterEq := ⟨HEq.rfl, HEq.rfl⟩
  wOk := hW
  chOk := hCh
  hcTie := hr.hcTie
  wtTie := hr.wtTie
  xgTie := hr.xgTie
  qNF := hr.qNF
  columnEvaluationOk := hr.columnEvaluationOk

end Pins

def selDHM (hDel : ∃ n : ℕ, D.s.Del = (n : ℚ)) (hh0 : ∃ n : ℕ, L.etaSz = (D.R.m : ℝ) * (n : ℝ)) :
    {p : ℕ × ℕ // D.s.Del = (p.1 : ℚ) ∧ L.etaSz = (D.R.m : ℝ) * (p.2 : ℝ)} :=
  ⟨(hDel.choose, hh0.choose), hDel.choose_spec, hh0.choose_spec⟩

end Formalism.L2.DIV.Member

end
