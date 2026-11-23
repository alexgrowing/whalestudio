import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallyConjunctionMono
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PinOfNTrue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FittingLaterStagesRowIsConstructionStateStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SizeParametersNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTypesOfTypesTrueReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FitsOL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GapRAllSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XiHTupTThird
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesWithLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigenReadThirdLocalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AgreeOfData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.E0ReadThirdLocalOfCoeffStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning

set_option maxHeartbeats 4000000 in

theorem pin_third (hL : GlobalTheory.Published.LocalLanglandsGL) (hP : PrN) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B}
    {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : LC hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ)
    (L : LocAll (lay0 (Dof x))) (hB : GlobalTheory.CoefDuty.Built l.a.A l.mt.M l.c.ch l.c.tp.tup big L) :
    ∃ Q : GlobalTheory.NPin.Pin hL (withLoc L), Q.cf = cfL L (cfOf x) ∧ Q.C = chL L l.c.ch ∧ HEq Q.tp (tpL L l.c.tp) ∧
      HEq Q.rep (repOf x.r.Y) ∧ HEq Q.M (mtL L l.mt.M) := by
  obtain ⟨Sp, ⟨Au⟩, ss⟩ := hB
  have hmt : MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
    have key : ∀ (xi : (Dof x).what₂.Tup → HChar (Dof x).host.E) (Q : (Dof x).what₂.places.Pl → Finset (PlE (Dof x).host)),
        MtInput (Dof x) l.mt.M (fun μ j => (cfOf x).mu0 j * xi μ) Q → l.c.tp.xi = xi → l.c.ch.Q = Q →
          MtInput (Dof x) l.mt.M l.c.tp.tup l.c.ch.Q := by
      intro xi Q h hx hQ
      subst hx hQ
      exact h
    exact key _ _ l.mt.mt l.c.xi_eq l.c.Q_eq
  let nt : NTrue hL (withLoc L) (cfL L (cfOf x)) (chL L l.c.ch) (tpL L l.c.tp) :=
    { D := Dof x, cf := cfOf x, jE := l.a.jE, A := l.a.A, cg := l.a.cg, au := l.a.au, rep := repOf x.r.Y, row := l.a.row,
      low := lowAll (Dof x), Pq := l.Pq, S := l.rat.S, hL := l.rat.In.hL, eig := l.rat.In.eig, θ := l.rat.In.θ, Bs := l.b.Bs,
      M := l.mt.M, C := l.c.ch, tp := l.c.tp, ch := l.c.side, mt := hmt, big := big, L := L, Sp := Sp, Au := Au, ss := ss,
      eq := rfl, pack := rfl }
  have hval : ValLL0 (withLoc L) (cfL L (cfOf x)) :=
    ⟨l.a.val.mu0, l.a.val.eta, l.a.val.chiPsi, l.a.val.del, l.a.val.del'⟩
  obtain ⟨Q, h1, h2, h3, h4, h5⟩ := GlobalTheory.NPin.pin_of_nTrue hL _ _ _ _ nt hval
    (fun σ σ' h => x.r.Y.eFT.injective (Formalism.IndefR.principalLevelFrame.rowRepR_inj _ _ _ h)) l.a.elem.star l.a.elem.int l.a.elem.split
    (GlobalTheory.ChebSplitDense.chebSplit_nd hP.what₂.cheb _)
  exact ⟨Q, h1, h2, h3, h4, h5⟩

end GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning

namespace GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
open GlobalTheory.HeightCounting.Fin3 GlobalTheory.HeightCounting.Up.RealOfReading

set_option maxHeartbeats 4000000 in

theorem cf_oL : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ T w P x => ∀ (l : LC hL x) (big : (Dof x).what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 (Dof x))), GlobalTheory.CoefDuty.Built l.a.A l.mt.M l.c.ch l.c.tp.tup big L → SumRepresentations.hypO (withLoc L) → ∀ (m : Moved (GlobalTheory.HeightCounting.Fin3.oL x L)), m.Copy → m.Coh → ∀ (s : Side0 (GlobalTheory.HeightCounting.Fin3.oL x L)) (r : ReadPk m s), r.Pin → m.z.R.C = cfL L (cfOf x) := by
  intro hL _ _
  exact StepW.of_all fun K B f T w _ _ _ P x l big L hB hO m _ _ s r _ => m.z.lev.C

set_option maxHeartbeats 4000000 in

theorem tied_third : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, PrN → GlobalTheory.NRows.HypothesesX → AllSt fun _ _ _ _ _ _ x => ∀ l : LC hL x, GlobalTheory.CoefDuty.EvO l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => SumRepresentations.hypO D' → Nonempty (GlobalTheory.NRows.Tied hL D') := by
  intro hL hP hX
  have H := ((GlobalTheory.HeightCounting.Up.ThirdFits.fits_oL hL hP hX).and (GlobalTheory.HeightCounting.Up.GapAllStates.gapR_allSt)).and (GlobalTheory.HeightCounting.Up.SizePar.exists_params.2.and ((cf_oL hL hP hX).and
    ((GlobalTheory.HeightCounting.Up.ThirdTied.xiH_tupT_third hL hP hX).and ((GlobalTheory.HeightCounting.Fin.types_withLoc hL hP hX).and ((GlobalTheory.T.exists_eigen_read_third_local hL hP hX).and
    ((GlobalTheory.HeightCounting.Up.ThirdAgree.agree_third hL hP hX).and (GlobalTheory.T.e0_read_third_local_of_coeff hL hP hX)))))))
  refine H.trans (StepW.of_all fun K B f T w _ _ h P x l => ?_)
  obtain ⟨⟨hfits, hgap⟩, hpar, hcf, htp, hty, hidx, hag, he0⟩ := h
  refine ⟨fun _ => ∅, fun L hB hO => ?_⟩
  obtain ⟨Q, h1, h2, h3, h4, h5⟩ := pin_third hL hP x l _ L hB
  obtain ⟨x', hx'⟩ := GlobalTheory.T.fittingLaterStages_row_is_constructionState hX.weil hX.ds hP.hc hP.decay K B f T w P (oL x L) (hfits P x l _ L hB hO) x.G_eq
    x.etaF (bkL L)
  obtain ⟨o, fits', G_eq', etaF', bk', m, cp, co, s, r, pn⟩ := x'
  dsimp only at hx'
  subst hx'
  have hC := hcf P x l _ L hB hO m cp co s r pn
  have ht := htp P x l _ L hB hO m cp co s r pn
  have hT := hty P x l _ L hB hO m cp co s r pn
  obtain ⟨Xd, E, ⟨labPi⟩⟩ := hidx P x l _ L hB hO m cp co s r pn
  have hg : GlobalTheory.LiftRows.Given m.z.R.toRealDat m.z.F.lv2 :=
    ⟨(GlobalTheory.CoreOfWeak.core_of_weak m.z.R m.z.F m.z.pins.char m.exAt).1, (hpar P x).2 L, m.intersectionNumber_baseChange.ok.ok2.irr,
      GlobalTheory.HeightCounting.goodTypes_of_typesTrue_real _ _ _ _ _ _ _ m.z.pins.char.base.lev hT, m.z.pins.keep.guard, hgap P x⟩
  obtain ⟨ag⟩ := hag P x l _ L hB hO m cp co s r pn hC Xd E labPi m.z.pins.char.base ht hg m.z.pins.char.fullP Q.rep h4
  have e0 := he0 P x l _ L hB hO m cp co s r pn hC Xd E labPi m.z.pins.char.base ht hg m.z.pins.char.fullP
  obtain ⟨T0, -, -⟩ := exists_tied Q (realOfRead m.z.R.toRealDat m.z.F.lv2 r.Y (tpL L l.c.tp) hC Xd E labPi
    m.z.pins.char.base ht hg m.z.pins.char.fullP) h1 h2 h3 (eq_of_heq h5) HEq.rfl ag e0
  exact ⟨T0⟩

end GlobalTheory.HeightCounting.Up.IntegralCoefficientPinning
