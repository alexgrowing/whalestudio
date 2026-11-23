import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsPassToMovedDivisionLatticesHeightsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsKeptChoiceUpperLatticeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralStageDataTransferLatticesHeightsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisionGeometryScalarsTransferSetDivisionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridStaircaseLatticeFirstColumnTransportStages
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.HeightCounting.Up

set_option maxHeartbeats 4000000

theorem kept_trans {D D' D'' : D7} {c : NChoice D} {c' : NChoice D'} {c'' : NChoice D''}
    (h : Kept c c') (h' : Kept c' c'') : Kept c c'' := by
  obtain ⟨g1, s1, f1, b1, t1, d1, q1, k1, p1⟩ := h
  obtain ⟨g2, s2, f2, b2, t2, d2, q2, k2, p2⟩ := h'
  refine ⟨?_, ?_, ?_, b1.trans b2, t1.trans t2, d1.trans d2, q1.trans q2, k1.trans k2, p1.trans p2⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := g1
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8⟩ := g2
    exact ⟨a1.trans e1, a2.trans e2, a3.trans e3, a4.trans e4, a5.trans e5, a6.trans e6, a7.trans e7, a8.trans e8⟩
  · cases s1; cases s2; constructor <;> (apply HEq.trans <;> assumption)
  · cases f1; cases f2; constructor <;> (apply HEq.trans <;> assumption)

theorem movable_prmR_nel : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) (Γ : GeoP), PositionMv (prmR (NEo hL cDep) SExt.none (geoCl Γ)).s := by
  intro hL cDep Γ
  intro K B f T w Z O x N h O' hO' col n
  obtain ⟨t', hs, hgeo, hpk, hobj, hrx⟩ := GlobalTheory.T.rows_pass_to_moved_divisionLatticesHeights K B f T w Z x.Wt O x.what₂ N h O' hO'
  obtain ⟨nch', xd', hkept, hnx, -, -, hmv⟩ := GlobalTheory.T.exists_kept_choice_upper_lattice hL K B f T w Z x.Wt Z.S N h O.nch O.xd
  obtain ⟨hn1, hn2⟩ := hnx rfl
  subst hO'
  have e1 : nch' = (O.tr N h).nch := eq_of_heq hn1
  have e2 : xd' = (O.tr N h).xd := eq_of_heq hn2
  subst e1 e2
  have hlp := GlobalTheory.Mem.GridMove.listPin_rowsSame cDep K.s.b K B f T w Z x.Wt Z.S N h O.p0 x.what₂ (O.tr N h).p0 t' hs x.nx.2.1.2.down
  obtain ⟨P, y, l, hls, hW, hk⟩ := x.nx.2.2.down
  obtain ⟨c⟩ := hmv O.p0 x.what₂ x.n (O.tr N h).p0 t' n hs hgeo ⟨x.nx.1, x.nx.2.1.1⟩
  obtain ⟨s⟩ := GlobalTheory.T.spectralStageData_transfer_lattices_heights K B f T w Z x.Wt O.p0 x.what₂ x.col.toColT N h (O.tr N h).p0 t' col.toColT hpk ⟨x.sx.1⟩
  obtain ⟨o⟩ := GlobalTheory.T.divisionGeometryScalars_transfer_setDivision Γ K B f T w Z x.Wt N h O (O.tr N h) rfl x.what₂ t' hs x.ox
  exact ⟨t', hobj x.obj, hrx ⟨x.rx⟩, ⟨⟨c.1, ⟨c.2, ⟨hlp⟩⟩, ⟨⟨P, y, l, hls, hW, kept_trans hk hkept⟩⟩⟩⟩, ⟨⟨s, PUnit.unit⟩⟩, ⟨o⟩⟩

end GlobalTheory.HeightCounting.Up

end
