import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnLocalDataTransportDivision
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConcreteSplitPrimeAutomorphicDataDivisionLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelTaylorSeriesPreservedDivisionLatticeChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaAutomorphicWeilDataPreservedDivisionLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionLocalDataPreservedDivisionLatticeChangeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTwistsThetaLatticesPreservedDivisionChangeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open GlobalTheory.Mem.Db GlobalTheory.Mem.Top.Bl.WitTr

set_option maxHeartbeats 16000000 in

theorem witMv_of_positionMv : ∀ 𝒮 : Slots, PositionMv 𝒮 → WitMv 𝒮 := by
  intro 𝒮 hS K B f T w Z O x N h hE
  have hR := GlobalTheory.T.concreteSplitPrimeAutomorphicData_divisionLatticeChange K.s (w.D Z) x.col.Gt x.col.cmp x.col.g.herm x.col.g.forms N h x.col.isRec
  let col := columnLocalDataTransportDivision w Z N h x.col hR
  obtain ⟨k, hk⟩ := GlobalTheory.T.kernelTaylorSeries_preserved_divisionLatticeChange w Z x.col.toColT O.X O.Gy x.ker0 x.ker N h hE
  let n := nchTTr w Z N h x.n
  obtain ⟨dv⟩ := GlobalTheory.T.divisionLocalData_preserved_divisionLatticeChange w Z x.n O.X N h x.div
  obtain ⟨th⟩ := GlobalTheory.T.thetaAutomorphicWeilData_preserved_divisionLatticeChange w Z x.n O.th N h x.th
  obtain ⟨t, hobj, ⟨rx⟩, ⟨nx⟩, ⟨sx⟩, ⟨ox⟩⟩ := hS K B f T w Z O x N h (O.tr N h) rfl col n
  have hker : (⟨(O.tr N h).gatT, (O.tr N h).cmp, (O.tr N h).tw, (O.tr N h).ker⟩ : Σ (Gt : GatTies (w.D (setDivZ Z N h)))
      (cmp : LatCmp (w.D (setDivZ Z N h))) (tw : TwForms (w.D (setDivZ Z N h))), KerFam (w.D (setDivZ Z N h)) Gt cmp tw (O.tr N h).Gy) =
      ⟨col.Gt, col.cmp, w.tw (setDivZ Z N h), kerTr w Z N h x.ker0⟩ := by
    have e := congrArg (fun s : Σ (Gt : GatTies (w.D Z)) (cmp : LatCmp (w.D Z)) (tw : TwForms (w.D Z)), KerFam (w.D Z) Gt cmp tw O.Gy =>
      (⟨gatTr (D := w.D Z) N h s.1, cmpTr (D := w.D Z) N h s.2.1, twTr (D := w.D Z) N h s.2.2.1,
        fun u v g => { s.2.2.2 u v g with }⟩ : Σ (Gt : GatTies (w.D (setDivZ Z N h))) (cmp : LatCmp (w.D (setDivZ Z N h)))
          (tw : TwForms (w.D (setDivZ Z N h))), KerFam (w.D (setDivZ Z N h)) Gt cmp tw (O.tr N h).Gy)) x.ker_eq
    exact e
  have herr : (O.tr N h).errX = Formalism.L2.Herm.toErrXS col.full.1 := by
    show errTr (D := w.D Z) N h O.errX = _
    rw [x.errX]; rfl
  refine ⟨{
      isOver := x.isOver
      forced := x.forced
      Wt := x.Wt
      pin := x.pin
      coh := x.coh
      vol := x.vol
      col := col
      what₂ := t
      rx := rx
      lev := x.lev
      errX := herr
      n := n
      nx := nx
      sx := sx
      ker0 := kerTr w Z N h x.ker0
      ker_eq := hker
      ker := k
      div := dv
      th := th
      obj := hobj
      ox := ox
      real := { x.real with }
      dsig_eq := x.dsig_eq
      gauge := x.gauge
      good := GlobalTheory.T.goodTwistsThetaLattices_preserved_divisionChange (w.D Z) O.nch O.xd N h x.good }, hk⟩

end GlobalTheory.Mem.Top.Bl

end
