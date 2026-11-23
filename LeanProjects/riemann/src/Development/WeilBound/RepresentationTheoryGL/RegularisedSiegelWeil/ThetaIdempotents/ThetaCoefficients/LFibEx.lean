import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibExB
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibExC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasuresStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhatStatement
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianFormulaStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LFibEx

variable {D : D7} {r : ℕ}

set_option maxHeartbeats 1000000 in
open GlobalTheory.CompanionTheory.SiegelND in
theorem _root_.PositivityTheory.Rg.Rsw.L.fibEx : FibEx := by
  intro D r V hr ψ hψ θ hθ μ hμ lam hlam b₀ hb₀
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  obtain ⟨μH, 𝓕, hμH, h𝓕, -⟩ := GlobalTheory.Published.SiegelOneVector.exists_normalised D.sp.cm.sig V.gram hCM hJ
  obtain ⟨dx, db, hdx, hdb, hW⟩ := GlobalTheory.T.exists_self_dual_siegel_weil_measures D r V ψ hψ μ hμ lam hlam
  have hT : ∀ a b, D.sp.cm.sig (b₀.1 b a) = b₀.1 a b := fun a b => by
    have := congrFun (congrFun b₀.2 a) b
    simpa [Matrix.transpose_apply, Matrix.map_apply] using this
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable D.host.F
  obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring _ _ D.sp.cm.sig hCM (AF D.host.F)
  have := hB r V.rank
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact _ _ D.sp.cm.sig hCM V.rank V.gram hJ (AF D.host.F)
  obtain ⟨ac, -, -, -⟩ := hact r
  have hTI := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_inv D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ μH 𝓕 hμH h𝓕 r b₀.1
  have hfin := thFin V hr μH 𝓕 hμH h𝓕 b₀.1 hT hb₀
  refine ⟨(thM V μH 𝓕 b₀.1).map (tupE D V.rank r), finE _, suppE V b₀.1 _ hTI.2,
    fun h => invE V _ h (ac.comp (continuous_const.prodMk continuous_id)).measurable (hTI.1 h), fun φ hφ => ?_⟩
  have hSB := GlobalTheory.T.schwartz_function_schwartz_bruhat D θ hθ V.rank r φ hφ
  have hI := thInt V hr μH 𝓕 hμH h𝓕 b₀.1 hT hb₀ _ hSB
  refine ⟨(tupE D V.rank r).measurableEmbedding.integrable_map_iff.2 hI, ?_⟩
  rw [hW φ b₀, (tupE D V.rank r).measurableEmbedding.integral_map]
  exact GlobalTheory.T.siegel_weil_hermitian_formula D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r hr ψ hψ dx hdx db hdb μH 𝓕 hμH h𝓕 _ hSB
    b₀.1 hT hb₀

end PositivityTheory.Rg.Rsw.L.LFibEx

end
