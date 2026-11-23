import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import ReciprocityTheory.Hypotheses.GalCoh
import Formalism.SharpRestriction.LevelLetterCocycles.ResidualIrreducibleOfTheoremThreePrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCanonicalModuleSuccessor
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PartsGiveDimensionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBisTer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowsOfInputsAndJumpsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrvG5OfLocalDualityStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointConditionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrvG6OfAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightParameterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrredOfCharpolyEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReducedFormOfLocalInputsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexHostE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmG2PairOfAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisSide
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleJOfParamsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroOfPrintsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfOverTwo
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts

noncomputable section

namespace GlobalTheory.CoreFacts

theorem main : GlobalTheory.NRows.Hypotheses₂ → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DepthZeroWild →
    GlobalTheory.Published.DepthZeroSupport → LocalFiniteness → LocalTateDuality → LocalEulerChar →
    ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), GlobalTheory.NRows.Inputs hL D → JumpsCard D.nd D.naut → Core D := by
  intro hP hc hd hw hs hF hT hE hL D I hJ
  have R : GlobalTheory.NRows.Rows D := GlobalTheory.T.rows_of_inputs_and_jumps hP hc hd hL D I hJ
  have at' : SumRepresentations.AdmAt D := I.admAt R.a R.b
  have p1 : SumRepresentations.Conclusion1 D := I.Conclusion1 (GlobalTheory.T.parts_give_dimension D) R.a R.b
  have g3 : AdmissibleThreePrime.LabelDegreeHypotheses D :=
    GlobalTheory.AdmTame.main D R.a.tie0 R.a.a2 R.a.a5 (GlobalTheory.TieLabAt.main hL D I.P).2.1
  have rb : ResidualIrreducibleRankR D :=
    Formalism.MainNotions.AdmissibleThreePrime.residual_irreducible_of_theorem_three_prime D ⟨R.a.tieLab, g3⟩ R.a.a5 (GlobalTheory.BrauerNesbittIrr.litBNIrr _) R.c.rho R.c.dz
  have adm : SumRepresentations.admitted D := ⟨at', (residualIrreducibility_forms_equivalent D).2 rb, I.isot⟩
  have ex : GlobalTheory.StringRepresentationDecomposition.RbEx D := GlobalTheory.T.residualRankPartExists_of_jointCondition D R.c.rho
  have g5 : SumRepresentations.ConclusionG5 D := GlobalTheory.T.conclusionG5_of_local_duality hF hT hE D adm ex
  have g6 : SumRepresentations.ConclusionG6 D := GlobalTheory.T.conclusionG6_of_admissible D adm ex
  have z : SumRepresentations.ConclusionZ D := (SumRepresentations.multiplicity_statement_iff_reduced D I.isot p1.2.2).2 (GlobalTheory.T.reduced_form_of_local_inputs hL D I R)
  have wt : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D := GlobalTheory.T.weight_parameter hL D I.P
  have bl : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D := GlobalTheory.BlockCharInf.main D I.P.cf I.P.C I.P.tp I.P.chr
  have rm : ∀ i : D.nd.Loc, Nonempty (RowMod D I.P.rep (D.nd.j i)) := fun i => by
    have hj := D.nd.j_range i
    obtain ⟨Y, -⟩ := GlobalTheory.RowModCanon.main hc hd hL D I.P I.X I.agree ⟨D.nd.j i - 1, by omega⟩ (D.nd.j i)
      (by simp only; omega)
    exact ⟨Y⟩
  exact
    { what₂ := R
      adm := adm
      Conclusion1 := p1
      Conclusion2 := ⟨g5, g6, z⟩
      rhoBar := rb
      g3p := g3
      weight := wt
      block := bl
      g2 := GlobalTheory.T.admG2_pair_of_admissible D R.a.tie0 I.adm1 R.a.a2 R.a.a5
      admJ := fun L h => GlobalTheory.T.admissible_J_of_params D L R.a.tie0 I.adm1 R.a.a2 R.a.a5 wt bl h
      muUnr := GlobalTheory.MuUnrTie.main hP.fin hL D I.P
      depthG := GlobalTheory.T.depth_zero_of_localLanglands hP hw hs hL D I.P rm
      bc := I.bc
      lam := I.lam }

end GlobalTheory.CoreFacts

end
