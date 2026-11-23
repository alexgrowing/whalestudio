import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParamStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftAllOfInputsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowLocalAllStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmptyStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoicesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeOfPublishedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up.ParCopy

set_option maxHeartbeats 4000000 in

theorem parIn_of_nTrue {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : NTrue hL D' cf' C' tp') (rep' : D'.what₂.FT → NG.FinTyp D'.host.E D'.R.r)
    (hrep : HEq nt.rep rep') :
    ∃ Rw : RowSide D', HEq Rw.locR nt.A.row.locR ∧ Nonempty (ParIn hL D' cf' rep' Rw) := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  obtain ⟨-, h2⟩ := Sigma.mk.inj_iff.mp pack
  obtain ⟨hcf, -⟩ := Sigma.mk.inj_iff.mp (eq_of_heq h2)
  subst hcf
  have hr : rep = rep' := eq_of_heq hrep
  subst hr
  let T : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { A.wdT with }
  let Rw : RowSide (withLoc L) := { A.row with }
  refine ⟨Rw, HEq.rfl, ⟨{ T := T, lab := A.lab, chr := { A.chr with }, cg := { cg with }, A := { A.au with }, au := au, row := row }⟩⟩

set_option maxHeartbeats 4000000 in

theorem mtInput_of_nTrue {hL : GlobalTheory.Published.LocalLanglandsGL} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : NTrue hL D' cf' C' tp') (M' : MtFam D') (hM : HEq (mtL nt.L nt.M) M') :
    ∃ tup Q, MtInput D' M' tup Q := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  have hm : mtL L M = M' := eq_of_heq hM
  subst hm
  exact ⟨tp.tup, C.Q, { mt with }⟩

set_option maxHeartbeats 4000000 in

theorem final (hN : PrN) (hL : GlobalTheory.Published.LocalLanglandsGL) {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'}
    {tp' : TupTied D' cf' C'} (nt : NTrue hL D' cf' C' tp') (Rw0 : RowSide D') (h0 : HEq Rw0.locR nt.A.row.locR)
    (hLift : LiftAll D' Rw0) (hLoc : ∀ σ, RowLoc D' Rw0 σ) (hEFK : SphericalInertData.HypEFK D') (hCM : SphericalInertData.HypCM D')
    (hDef : ∀ j, 1 ≤ j → j ≤ D'.R.m → (D'.sp.V j).IsDefinite) (Rw : RowSide D') (hRw : HEq Rw.locR nt.A.row.locR) :
    GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam D' Rw := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hk, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := nt
  subst eq
  have e0 : Rw0.locR = A.row.locR := eq_of_heq h0
  have e1 : Rw.locR = A.row.locR := eq_of_heq hRw
  have hpar : ParIn hL D cf rep A.row := ⟨A.wdT, A.lab, A.chr, cg, A.au, au, row⟩
  have hLaws := GlobalTheory.T.parameter_laws_empty hN hL D cf rep A.row A.bare hpar
  have hconds := GlobalTheory.T.base_change_of_hypotheses hN.bc hN.what₂.bern hN.ds hN.gen hN.std hL D A.wdT A.au cg au
  have hLift' : LiftAll D A.row := by
    intro j h1 h2 σ hσ
    obtain ⟨π, μ, hl⟩ := hLift j h1 h2 σ hσ
    refine ⟨π, μ, ⟨hl.csd, hl.unr, hl.sph, fun w hw => ?_, hl.eta, hl.inf⟩⟩
    have := hl.loc w hw
    rw [e0] at this
    exact this
  have hLoc' : ∀ σ, RowLoc D A.row σ := by
    intro σ w hw hk
    have := hLoc σ w hw hk
    rw [e0] at this
    exact this
  have hG := GlobalTheory.T.good_row_cusp_param D A.row hLaws hconds hEFK hCM hDef hLift' hLoc'
  intro j h1 h2 σ hσ hg
  obtain ⟨π, hπ⟩ := hG j h1 h2 σ hσ hg
  refine ⟨π, hπ.1, hπ.2.1, fun w hw => ?_, hπ.2.2.2⟩
  rw [e1]
  exact hπ.2.2.1 w hw

end GlobalTheory.HeightCounting.Up.ParCopy

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.HeightCounting.Up.ParCopy in

theorem goodRowCuspParam_atMem : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL (fun _ _ _ _ w Z _ _ _ _ _ c =>
    ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) := by
  intro hN hL
  have hlift := GlobalTheory.T.lift_all_of_inputs hN hL
  have hloc := GlobalTheory.T.row_local_all hN hL
  have hsz := GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices
  refine EvG.imp ((hlift.inter hloc).inter hsz) fun K _ _ _ _ H => ?_
  refine large₂.imp ((H.1.1.inter H.1.2).inter H.2) fun B f T _ h => ?_
  intro hKP w Z Wt p0 t nch n xd c hE _ hpin Rw hRw
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  obtain ⟨e⟩ := hE
  have e' : NMore (D := (w.st Z).toD7) c.row t.r.z.geo xd := e
  obtain ⟨Rw0, hRw0, ⟨hpar⟩⟩ := parIn_of_nTrue c.a.nt _ c.row.rep_eq
  obtain ⟨tup, Q, hmt⟩ := mtInput_of_nTrue c.a.nt c.a.all.gal.mt c.a.mt_eq
  have hLift := h1 hKP w hpin Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt Rw0 hpar _ tup Q e'.ad hmt
  have hLoc := h2 hKP w hpin Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt Rw0 hpar
  obtain ⟨-, -, -, hEFK, hCM, hDef, -⟩ := h3 hKP T w Z
  exact final hN hL c.a.nt Rw0 hRw0 hLift hLoc hEFK hCM hDef Rw hRw

end GlobalTheory.HeightCounting.Up
