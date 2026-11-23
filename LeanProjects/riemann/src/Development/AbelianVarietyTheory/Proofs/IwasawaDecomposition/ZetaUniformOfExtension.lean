import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerEntTiedTrueEnt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStdFStdLvC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsOfHeqData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReFaceScalarsErrorsReadings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IotaStarProjectionQsp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionPairingRationalOnRationalPoints
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 4000000 in

theorem readC_reFace_updS (R : RealDat3 D A3 Ks) (F : Face3 D A3) (X0 : BaseLevelRowSide D)
    (Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 F.P1 F.ψ1 Zs)) (Sp Sp' : ∀ Zs, SPer (Dc Zs))
    (Zsc Zsc' : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3) (kap : ℝ) (lam : type_of% R.lam3)
    (err : type_of% (R.updS kap lam).err0) {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}
    (C : ReadC R (reFace F Dc Sp Zsc) X0 Y)
    (Y₁ : Read (A3 := A3) ((R.updS kap lam).withErr err).toRealDat F.lv2 X0) (h1 : Y₁.tup = Y.tup) (h2 : HEq Y₁.jA Y.jA) :
    Nonempty (ReadC ((R.updS kap lam).withErr err) (reFace F Dc Sp' Zsc') X0 Y₁) := by
  have key : ∀ (tp : T → D.what₂.Tup)
      (j : ∀ t, (Fin (rDim D A3.A F.P1 F.ψ1 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Amb (tp t)), tp = Y.tup → HEq j Y.jA →
      ∀ (u : D.what₂.Word) (t : T) (x : Fin ((Dc (R.toCx3 F).zs).a (C.wU u)) → D.what₂.LL)
        (f : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV t) → D.what₂.LL),
        D.what₂.embLL ((Dc (R.toCx3 F).zs).Pt (C.wU u) t x f) =
          D.what₂.perCol u (tp t) (D.jN u (C.eNu u x)) (j t ((rV0 D A3.A F.P1 F.ψ1 t).mulVec f)) := by
    intro tp j h1 h2
    subst h1
    cases h2
    exact C.pt
  exact ⟨⟨C.wU, C.bij, C.eNu, C.NuC, C.nu, key Y₁.tup Y₁.jA h1 h2⟩⟩

end GlobalTheory.Mem.R3

open Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev GlobalTheory.Mem.R3 in
set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.Top.Bl.zeU_prmR_NEb : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ZeU (prmR N S Γ).s := by
  intro hPr hL N S Γ hN K q
  have hK : ∃ t : Formalism.L2.Ker.KerEntTied q.O.ex, KPin q t := by
    obtain ⟨B, f, T, w, Z, O, x⟩ := q
    obtain ⟨L, gatT, Gx, Gy, Kc, X, cX, ex⟩ := O
    obtain ⟨lev, th, th_io, cmp, lat, tw, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch, nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ := ex
    obtain ⟨isOver, forced, Wt, pin, coh, vol, col, what₂, rx, hlev, herrX, n, nx, sx, ker0, ker_eq, kT, div, thT, obj, ox, real, dsig_eq, gaugeG, good⟩ := x
    simp only [ofObj, extraObj] at ker_eq
    cases ker_eq
    obtain ⟨t1, s1, o1, e1, a1, p1⟩ := TC.kerEntTied_true_ent w.I w.ok w.pins w.l Z L col.Gt Gx Gy Kc X cX
      ⟨lev, th, th_io, col.cmp, lat, w.tw Z, ker, ep_def, ep_tie, kapI_def, fills_all, nu_unserved, idx, kap_def, lam_def, kapR_def, errX, err, nch,
        nch_tie, xd, p0, rationalRoots_def, amb, amb0, fdef, duStar_def, Dstar_def, gauge, gauge_def⟩ kT.O kT.E div.Qp kT.std
      kT.unf kT.ok kT.served
    exact ⟨t1, (StdModel.stdKer_iff w.I w.l Z t1).2 s1, o1, heq_of_eq e1, a1, p1⟩
  obtain ⟨t, ht⟩ := hK
  obtain ⟨Dc, Sp₀, Zsc₀, C₀, -⟩ := GlobalTheory.Mem.R3.SelC.cols_of_witnesses _ K q t ht ⟨q.x.rx⟩
  obtain ⟨kap, lam, err, hP, hH, -, -, -, Y', Z', htup, -, hjA, -⟩ := GlobalTheory.Mem.R3.reFace_scalars_errors_readings _ _ _ _ _ _ _
    q.x.what₂.r.z.R q.x.what₂.r.z.F q.x.what₂.r.z.cG _ q.x.what₂.r.Y q.x.what₂.r.Z Dc Sp₀ q.x.what₂.r.z.F.Zsc (fun _ => Or.inl rfl)
    q.x.what₂.r.z.pins q.x.what₂.r.intersectionNumber_baseChange
  obtain ⟨C'⟩ := GlobalTheory.Mem.R3.readC_reFace_updS _ _ _ Dc Sp₀ Sp₀ Zsc₀ q.x.what₂.r.z.F.Zsc kap lam err C₀ Y' htup hjA
  obtain ⟨nb⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2
  have hBk : BkLaw (q.w.D q.Z) := nb.2.down
  have hRat := GlobalTheory.Mem.R3.divisionPairing_rational_on_rationalPoints hPr (q.w.st q.Z).toD7 _ _ _ _ _ _ _ _ _ _ Y' Z' C' hP hH
  exact GlobalTheory.Mem.R3.zeTied_of_read hPr (q.w.st q.Z).toD7 _ _ _ _ _ _ _ _ _ _ Y' Z' C' hP hH (hBk hRat)
