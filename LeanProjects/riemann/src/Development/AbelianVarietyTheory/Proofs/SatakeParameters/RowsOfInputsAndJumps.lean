import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenGoodOfAdmissibilityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenStringOfAgreementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyJoinOfAgreementStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftSpacesRankConstAndLocalisationScalarsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsGiveDimensionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsAOfJumpCountStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsBAndLocalLiftsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsCOfLocalLiftsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeNonzeroRecursionOfEigenStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowsAll

theorem main : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), GlobalTheory.NRows.Inputs hL D → JumpsCard D.nd D.naut → GlobalTheory.NRows.Rows D := by
  intro hP hHC hCusp hL D I hJ
  have a : GlobalTheory.NRows.RowsA D := GlobalTheory.T.rows_a_of_jump_count hP hL D I.P hJ
  obtain ⟨J⟩ := GlobalTheory.T.nonempty_join_of_agreement hHC hCusp hL D I.P I.X I.agree
  obtain ⟨lamLoc, rank⟩ := GlobalTheory.T.thetaLiftSpaces_rank_const_and_localisation_scalars D I.isot I.lam
  obtain ⟨b, trip⟩ := GlobalTheory.T.rows_b_and_local_lifts hP hL D I.P J a I.adm1 lamLoc
  have Conclusion1 : Formalism.MainNotions.SumRepresentations.Conclusion1 D := I.Conclusion1 (GlobalTheory.T.parts_give_dimension D) a b
  have c : GlobalTheory.NRows.RowsC D := GlobalTheory.T.rows_c_of_local_lifts hL D I.P J a b I.adm1 I.isot Conclusion1 trip
  refine ⟨a, b, c, fun i => ?_, rank⟩
  exact GlobalTheory.T.type_nonzero_recursion_of_eigen hL D I.P I.X I.agree I.typeNZ i
    (GlobalTheory.T.eigen_string_of_agreement hP.fin hL D I.P I.X I.agree Conclusion1.1 a.temp a.tieLab i)
    (GlobalTheory.T.eigen_good_of_admissibility hL D I.P I.X Conclusion1.1 a.tieLab I.mtPar I.adm1 a.tie0 b.a4 a.a5 I.e0loc I.e0read i)

end GlobalTheory.RowsAll
