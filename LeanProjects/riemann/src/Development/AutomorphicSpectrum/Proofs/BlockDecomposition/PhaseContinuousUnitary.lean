import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

theorem psiFin_continuous_unit (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) : Continuous (psiFin F ψ) ∧ ∀ y, ‖psiFin F ψ y‖ = 1 := by
  refine ⟨?_, fun y => hψ.2.1 _⟩
  have : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
  exact hψ.1.comp this

set_option maxHeartbeats 1000000 in

theorem phaseB_pairB_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (b : HermR (Af F) σ n),
    Continuous (phaseB σ J (psiFin F ψ) b) ∧ (∀ X, ‖phaseB σ J (psiFin F ψ) b X‖ = 1) ∧
    ∀ X, Continuous (pairB σ J (psiFin F ψ) b X) := by
  intro F E _ _ _ _ _ σ hσ M J n ψ hψ b
  obtain ⟨a1, a2, a3, -, -, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : LocallyCompactSpace (Af F) := a1
  haveI : SecondCountableTopology (Af F) := a2
  haveI : T2Space (Af F) := a3
  obtain ⟨t1, -, -, -, hs, htr, -, -, -, hG⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Af F)
  haveI : IsTopologicalRing (Af F ⊗[F] E) := t1
  obtain ⟨hc, hn⟩ := psiFin_continuous_unit F ψ hψ
  refine ⟨?_, fun X => hn _, fun X => ?_⟩
  · refine hc.comp (continuous_const.mul (htr.comp (Continuous.matrix_trace
      (Continuous.matrix_mul continuous_const (hG n M J)))))
  · refine hc.comp (htr.comp (Continuous.matrix_trace
      (Continuous.matrix_mul continuous_const ?_)))
    refine continuous_matrix fun a c => ?_
    simp only [gram2, hR, Formalism.UG.hform]
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact continuous_const.mul ((continuous_apply j).comp (continuous_apply c))

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
