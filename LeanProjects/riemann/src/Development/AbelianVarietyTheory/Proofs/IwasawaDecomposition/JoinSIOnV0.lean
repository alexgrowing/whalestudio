import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSI
import Formalism.LocalToGlobal.IndefiniteReal.RealPins
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeqIotaIffEqTransCastAdelicGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelJoinOnV0ThreeStatement

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.JTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
  {R : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def JoinPin (Q : RealT R P Dcf Spf Zscf S Ks) : Prop :=
  ∃ eE : D.what₂.EE →ₗ[ℂ] Q.Rl.HE.H,
    (∀ y y', HEq y y' → eE (D.jEE (P.I.eRR y)) =
      Tw.out (s := Formalism.L2.SG.JoinSI.twQ P) (E := Q.Rl.HE.H)
        ((Formalism.L2.SG.JoinSI.cx Q).iC Q.F.cr true P.A3.A.μ0 (cpt P.A3.A.v0.embedding y'))) ∧
    ∀ hF : Formalism.L2.SG.PackageTie2.FinX S.Y, GlobalTheory.Mem.SRe.RowJ Q.Rl.toRealDat eE S.X S.inst S.G Q.tS (Formalism.L2.SG.JoinSI.jOf S hF)

theorem core {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    (Rl : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ) (hOk : A3.fam3.Ok3 n) (hSep : A3.fam3.TypesSep3)
    (hCh : Rl.WeakCharacterisation F) (hPrim : PrimRows3 Rl F) (hSchur : SchurAll D) (hSig : (D.sp.Y 0).SigOK)
    (Zs : DefSub A3.fam3.amb3) (hzs : (Rl.toCx3 F).zs = Zs)
    (S0 : IndefData (A3.side3 F.P0 F.ψ0 Zs)) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs))
    (hs1 : HEq ((Rl.toCx3 F).data F.cr true) S1)
    (Dc : DefCols (A3.side3 F.P1 F.ψ1 Zs)) (hdc : F.Dc Zs = Dc) (Sp : SPer Dc) (hsp : HEq (F.Sp Zs) Sp)
    (p0 : BaseLevelRowSide D) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 Zs S0 S1 p0 Dc)
    (hDef : DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 Zs S0 S1 p0 C NuC I)
    (hDivR : DivRows3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 Zs S0 S1 p0 C NuC I)
    (hPt : ∀ (u : D.what₂.Word) (x : Fin (Dc.a (I.wU u)) → D.what₂.LL)
      (y : Fin ((A3.side3 F.P1 F.ψ1 Zs).nV A3.A.μ0) → D.what₂.LL),
      D.what₂.embLL (Dc.Pt (I.wU u) A3.A.μ0 x y) =
        D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y)))
    (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Gd : GoodOp St) (hK : St.LevelSubgroupCharacter)
    (pw : ∀ u, PerW St hK u) (wdD : Dc.Mem → D.what₂.Word) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)
    (hwdD : ∀ u, wdD (I.wU u) = u)
    (hSp : HEq Sp (spOf (twAt D.what₂.embLL A3.A.v0) Dc hK Gd wdD (fun x => pw (wdD x)) bR))
    (hbR : ∀ u i, HEq (bR (I.wU u) i) (D.eMu u (D.jN u (I.eNu u (Pi.single i 1)))))
    (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hEv : EvalTieT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true)) St Gd
      (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c)
    (sEE : (Rl.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (Rl.toCx3 F).zs).Sp.HH)
    (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) Rl.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX St)) (κS : ℂ)
    (hsE : HEq sEE sEEc) (hκ : κS ≠ 0)
    (hsee : ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) Rl.HE.H)
      (hx : Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true))),
      sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) (κS • sEEofTT (Rl.MY 0) Rl.ν0 Rl.fd0
        (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c
        ⟨Rl.HE.e (Tw.out x), hx⟩))
    (eE : D.what₂.EE →ₗ[ℂ] Rl.HE.H)
    (hRead : ∀ y y', HEq y y' → eE (D.jEE (I.eRR y)) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := Rl.HE.H)
      ((Rl.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y'))) :
    ∃ (Rd : GlobalTheory.Mem.SJ.Read D (Rl.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0)) (M : GlobalTheory.Mem.SJ.Seam Rd F.cr),
      HEq Rd.wU I.wU ∧ M.ChainTie ∧ M.GoodPartHasComplexCoordinates ∧ M.RowTie (F.eV (Rl.toCx3 F).zs) ∧ M.ColNorm ∧
      (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ ∧
      ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St Gd) (v₀ : (Rl.MY 0).Vec) (a : ℂ),
        (∀ x, ((j x : EEC St Gd) : L2X St) =ᵐ[muX St]
          fun g => a * ev (Rl.MY 0) v₀ (Rl.HE.e (eE x)) ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm g * t)) →
        ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (x : D.what₂.EE) (φ : D.what₂.Mu u) (T' : Cu St u hK),
          colDictL St (pw u).Tr hK T' = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) →
          ⟪sEE (M.eR x), (F.fc (Rl.toCx3 F).zs).Sp.Pu (Rd.wU u)
              (GlobalTheory.Mem.SJ.cjv (twAt D.what₂.embLL A3.A.v0) (M.cφ u φ))⟫_ℂ =
            cj (twAt D.what₂.embLL A3.A.v0) (κ * ⟪((conjHH St Gd (j x) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T'⟫_ℂ) := by
  subst hzs
  subst hdc
  obtain rfl := eq_of_heq hs1
  obtain rfl := eq_of_heq hsp
  obtain ⟨Rd, M, hw, h1, h2, h3, h4, hon, hT⟩ :=
    GlobalTheory.T.kernel_join_on_V0_three D G Pl0 I0 T A3 Ks Rl F n hOk hSep hCh hPrim hSchur hSig S0 p0 C NuC I hDef hDivR hPt
  exact ⟨Rd, M, hw, h1, h2, h3, h4, hon, fun j v₀ a hj => hT St h Gd hK pw wdD bR hwdD (eq_of_heq hSp) hbR t c hEv
    sEE sEEc κS hsE hκ hsee eE (fun y => hRead y y HEq.rfl) j v₀ a hj⟩

theorem bR_heq (Q : RealT R P Dcf Spf Zscf S Ks) (hPin : RealPins Q) (u : D.what₂.Word) (i : Fin (P.Dc.a (P.I.wU u))) :
    HEq (Q.bR (P.I.wU u) i) (D.eMu u (D.jN u (P.I.eNu u (Pi.single i 1)))) := by
  refine HEq.trans (heq_of_eq (hPin.bR_read (P.I.wU u) i)) ?_
  have key : ∀ (w : D.what₂.Word) (hw : w = u) (hc : P.Dc.a (P.I.wU u) = P.Dc.a (P.I.wU w)),
      HEq (D.eMu w (D.jN w (P.I.eNu w (Pi.single (Fin.cast hc i) 1))))
        (D.eMu u (D.jN u (P.I.eNu u (Pi.single i 1)))) := by
    intro w hw hc
    subst hw
    rfl
  exact key _ (Q.wdD_wU u) _

end GlobalTheory.Mem.JTop
