import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameIntegralThetaMeasureFormulaStatement
import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelWeilFreeOfBlockNonemptyFramesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalizationStatement
import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.BlockCoefficientLocalGlobalFactorStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WeilSiegel.Frame

theorem siegel_frame : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → (∃ x : Matrix (Fin V.rank) (Fin r) D.host.E, x.rank = r ∧ gramQ V x = β.1) → IfrB V ν φ β = W ψ V μ lam φ β := by
  intro D r V ψ θ μ lam ν φ hH t β hNF hx
  obtain ⟨hr, hψ, hθ, hμ, hlam, hν, hφ, habs⟩ := id hH
  obtain ⟨x, hxr, hxg⟩ := hx
  have hCM : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt D.host.F D.host.E D.sp.cm.sig := Formalism.MainNotions.UnusedSlot34.isCMExt_D D
  have hJ : HeckeCharacterZeroLocus.SiegelWeilU.IsHermND D.sp.cm.sig V.gram := isHermND_gram V
  obtain ⟨⟨𝓕, h𝓕⟩, -⟩ := GlobalTheory.Mem.Vol.fundamentalDomain_adelicUnitary D.host.F D.host.E D.sp.cm.sig V.rank V.gram ν hν
  have hfr : (framesE D.sp.cm.sig V.gram β.1).Nonempty := by
    refine ⟨fun a i => x i a, ?_⟩
    rw [trM_mem_framesE_iff]
    exact ⟨hxr, hxg⟩
  obtain ⟨d, b, laminf, lamv, minf, m, h1, h2, h3, h4⟩ :=
    GlobalTheory.T.exists_tamagawa_measure_normalization D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r
  have hS := GlobalTheory.T.siegelWeil_free_of_block_nonempty_frames D.host.F D.host.E D.sp.cm.sig hCM V.rank V.gram hJ r t β.1 (hermE_symm β) hNF hr hfr
    d b laminf lamv h1 h2 ν 𝓕 hν h𝓕 minf m h3 h4
  obtain ⟨hi, he⟩ := GlobalTheory.T.frame_integral_theta_measure_formula D r V θ hθ ν hν 𝓕 h𝓕 φ hφ habs β
  rw [he]
  exact (GlobalTheory.T.block_coefficient_local_global_factor D r V ψ θ μ lam ν φ hH t β hNF d b laminf lamv minf m h1 h2 h3 h4 _ hS hi).symm

end GlobalTheory.CompanionTheory.WeilSiegel.Frame
