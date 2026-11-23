import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsCrisPOfIsCrisDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsDataStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisOneSubFrobeniusSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjectiveStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc

namespace GlobalTheory.FundSeq

theorem ontoAt (l : ℕ) [Fact l.Prime] : OntoAt l := by
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_localPeriodRingsData l
  exact ontoAt_of_core C (GlobalTheory.T.bcris_one_sub_frobenius_surjective l C) (GlobalTheory.T.fundamental_map_surjective l C)

theorem surjective_half (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.LocalSituation.adm1 D :=
  surjective_half_of_onto (fun l _ => ontoAt l) D

end GlobalTheory.FundSeq
