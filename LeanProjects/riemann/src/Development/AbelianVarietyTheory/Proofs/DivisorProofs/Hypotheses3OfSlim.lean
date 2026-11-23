import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Definitions.Divisors.NefProd
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcove
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LandherrStOfHasseNormSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PrincipalPolarisationUniqueSection
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartsOfSiegelOfForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusOfFormMixedProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectionFormulaAndChernDegreeOfHeightProjectio
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefNumericsOfRiemannRoch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamOfDualityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrothendieckDeformationOfLifting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeOneTmulEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TamagawaSpecialUnitaryOfSuStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.AbelianVarietyTorsionCardEqPowProof

namespace GlobalTheory.CovTop

theorem hypotheses3_of_slim : Slim → GlobalTheory.Published.CubeTheorem →
    GlobalTheory.Published.ScholzeWeinsteinB ∧ Hypotheses3 ∧ GlobalTheory.CovHt.HypothesesH := by
  intro h hcube
  have p4 : GlobalTheory.Published.ArCalc := GlobalTheory.Published.arCalc_of_form_mix_projection h.arForm h.arMix h.htProj
  have p5 : GlobalTheory.Published.AbelianDeRham := GlobalTheory.T.abelian_de_rham_of_duality hcube h.dr h.crys h.dual h.poinc
  have g1 : GlobalTheory.Published.GrothendieckDeformation := GlobalTheory.Published.grothendieckDeformation_of_lifting p5 h.lift
  have hs : GlobalTheory.Published.HasseNormSt := GlobalTheory.QNorm.hasseNormSt
  refine ⟨GlobalTheory.SatForm.scholzeWeinsteinB_of_subspaces h.prism h.pdiv, ?_, ?_⟩
  · refine ⟨?_, g1, h.chowCut⟩
    exact
      { p1 := h.canExt.toroidalCompactification
        p2 := h.volGe
        p3 := h.hs.volNef
        p4 := p4
        p5 := p5
        p6 := GlobalTheory.T.tamagawa_special_unitary_of_su h.tam
        p8 := h.ray
        p12 := GlobalTheory.SS.semistableReductionSt
        p13 := h.approx
        p14 := h.green
        p16 := ⟨h.good, h.push⟩
        p19 := GlobalTheory.LocalQuad.landherrSt_of_hasseNormSt hs
        p20 := hs
        p22 := h.homExt
        p23 := GlobalTheory.Alc.inducedSimpleLowestAlcove
        p25 := GlobalTheory.AbLaw.principalPolarisation_unique_section
        p26 := GlobalTheory.abMulN_holds
        q1 := g1.grothendieckMessing
        q3 := h.canExt
        q4 := h.prism
        q6 := h.kv
        q7 := GlobalTheory.Published.nefNumerics_of_product_of_riemannRoch h.nefProd h.nefRR
        q8 := h.l2
        q9 := h.hs
        q10 := GlobalTheory.Published.chowFormExists_holds
        q11 := GlobalTheory.Published.cycleHeights_of_arCalc p4
        q13 := GlobalTheory.Published.serreHolomorphicSections_holds
        q15 := ⟨h.nadel, h.nonKlt⟩
        q16 := h.princ
        q18 := h.alg }
  · exact ⟨h.sieg, h.fan, GlobalTheory.Published.toroidalCharts_of_siegel_of_forFan h.sieg h.fan,
      GlobalTheory.Published.arDegree_of_heightProjection h.htProj h.chern⟩

end GlobalTheory.CovTop
