import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunsHoldOfTies
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeavesSupSpanData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasIndexBoundOfRuns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumOfFjEqOfRecord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafDepthAllRecord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunNumericalConditionsHoldAlongFamilyStatement

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

section Comparison₂

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem indefinitePoint_splitPartContent_eq_forcedContent (p : PtAt ex Csz) (C CH : ℝ) :
    Formalism.L2.Indef.Tree.DepthCond.ContentEqualsDatumContent ((R2 p).num (F2 p) C CH) (GlobalTheory.RunDepth.numOf D L) (fun j : Fin D.R.m => (j : ℕ) + 1) := by
  intro w j
  rw [numOf_Fj_eq_ofRecord D L p.Del p.h0 p.hDel p.hh0]
  rfl

end Comparison₂

theorem geoSt_of_pageSt : PageSt → GeoSt := by
  intro hP
  obtain ⟨CK, xa, HR⟩ := runsHold_of_ties
  obtain ⟨xb, HL⟩ := leaves_sup_span_data CK
  obtain ⟨Cd, HD⟩ := leafDepth_all_record
  refine ((hP.and (GlobalTheory.T.runNumericalConditions_hold_along_family xa)).and (GlobalTheory.T.runNumericalConditions_hold_along_family xb)).imp fun Fm CH _ H => ?_
  obtain ⟨⟨⟨c0, hc0⟩, ⟨ya, hya⟩⟩, ⟨yb, hyb⟩⟩ := H
  refine ⟨max c0 Cd, fun c hc hbad => ?_⟩
  obtain ⟨x0, hx0⟩ := hc0 c ((le_max_left _ _).trans hc) hbad
  refine ⟨max x0 (max ya yb), fun x hx hle i p hrows hmore r O hrec => ?_⟩
  have h0 : x0 ≤ x := (le_max_left _ _).trans hle
  have ha : ya ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have hb : yb ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  obtain ⟨hPg, hSz, -, -, -, -, hOb, -, -⟩ := hx0 x hx h0 i p hrows hmore r O hrec
  obtain ⟨pna, hx3, hkb, hxe, -⟩ := hya x hx ha i
  obtain ⟨pnb, -, -, -, -⟩ := hyb x hx hb i
  have hcore := hmore.2.1
  have hown := hrec.2
  have hch := (GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hrows hmore.1).1
  have hRH := HR _ _ _ _ _ _ _ (F2 p) _ _ _ _ _ _ (Fm.ex x hx i).kap_def _ _ hcore hrec.1.ok hown pna
  obtain ⟨hSup, hSpan, hS, hData⟩ := HL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ O hrec.1 hcore hown pnb hRH hch.grp
    hch.tup.mu_conj hch.tup.mu_off hch.tup.mu_ne
  refine ⟨hSup, hSpan, hS, hData, hasIndexBound_of_runs CK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ O hrec.1 hcore hown hRH hSup hSpan
    hOb, fun C CH' => ?_⟩
  exact HD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ O hrec.1 _ hPg hSz hx3 hkb (indefinitePoint_splitPartContent_eq_forcedContent p C CH')
    ((le_max_right _ _).trans hc) (le_of_eq pna.2.1.symm) hxe

end GlobalTheory.BigOn
