import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalRingCardinality.DataKap
import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreCompatibleAdelicDataCharactersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReferenceTupleThetaComparisonNormalisedDatStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantsThetaComparisonAllTuplesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreConstantsBaseSolutionEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaComparisonDataIndependentOfAlgebraicFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfRealisationGeometricActionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegralStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoHalfTop

theorem exists_geoHalf : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), VolTieG D → LawsJ T → LawsCore T.toCore → AlgTie T → T.pb = R.C.P.pb → PreChar R → ValKs R → FrameKs T.Q.c.F R.MW → Formalism.L2.Host.ValLL D R.C → Finite T0 → QGuard R → (∀ i, VStd D i) → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → ∃ dict mu chiW x₀ cE nW FW, ∃ B : GeoHalf (reCore T dict mu chiW x₀ cE) (updFW R nW FW) (fun _ => 1), B.κ = kapTop D ∧ InGeo B ∧ Fired (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) ∧ (∀ i, OneMapRowR (reCore T dict mu chiW x₀ cE) (updFW R nW FW) B.κ B.v₀ B.O (fun _ => 1) i) ∧ IoExt (updFW R nW FW) ∧ PreChar (updFW R nW FW) ∧ (updFW R nW FW).grp_chiW ∧ (updFW R nW FW).LUnif ∧ (updFW R nW FW).LIntegral ∧ LawsCore (reCore T dict mu chiW x₀ cE).toCore := by
  intro hC D G _ _ Pl0 T0 A T _ R hvol hJ hcore halg hpb hpre hval hfr hLL hfin hQ hstd hn
  obtain ⟨dict, mu, chiW, x₀, htie, hcore₁⟩ := GlobalTheory.T.exists_core_compatible_adelicData_characters D G Pl0 T0 A T R hvol hJ hcore halg hpre.lev hval hfr
  have hio : IoExt R := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ R hpre.lev hpre.fam hpre.models hpre.thP
  obtain ⟨O, hO⟩ := GlobalTheory.T.exists_referenceTuple_thetaComparison_normalisedData D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) hpre hLL htie hpb hQ hstd
  choose cc hcc0 hcc using fun i => GlobalTheory.T.exists_constants_theta_comparison_all_tuples D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) O hpre htie
    hpb hfin hQ hio i (hstd i) (hO i)
  obtain ⟨cE, hcE, htie₂, hO₂, hF⟩ := GlobalTheory.T.exists_core_constants_base_solution_equivariant D G Pl0 T0 A (reCore T dict mu chiW x₀ T.cE) R (kapTop D) (v0 R) O cc
    hpre.lev htie hpb hO hcc0
  obtain ⟨B, hκ, hv, hFB, hpre₂, hchi⟩ := GlobalTheory.T.exists_geometric_half_realisation_geometric_action D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R) O
    (fun _ => 1) hpre htie₂ hO₂ hF
  obtain ⟨hin, hU, hI⟩ := GlobalTheory.T.geometricHalf_coreForms_uniformisation_integral hC D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) _ (fun _ => 1) B hpre₂ hchi hpb hn
  refine ⟨dict, mu, chiW, x₀, cE, _, _, B, hκ, hin, hFB, fun i => ⟨⟨_, _, hFB.1 i⟩, fun _ => ?_⟩,
    GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ _ hpre₂.lev hpre₂.fam hpre₂.models hpre₂.thP, hpre₂, hchi, hU, hI, hcore₁⟩
  obtain ⟨O', h1, h2, h3⟩ := hcc i
  obtain ⟨O'', e1, -, p1, p2⟩ := GlobalTheory.T.theta_comparison_data_independent_of_algebraic_forms D G Pl0 T0 A (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R)
    (nTop (reCore T dict mu chiW x₀ cE) (kapTop D)) (formsGeo (reCore T dict mu chiW x₀ cE) R (kapTop D) (v0 R) O) i T0 id O'
  rw [hκ, hv]
  refine ⟨O'', ?_, p1 h2, ?_⟩
  · rw [e1]; exact h1
  · rw [← hcE i] at h3
    exact p2 _ _ h3

end GlobalTheory.GeoHalfTop

end
