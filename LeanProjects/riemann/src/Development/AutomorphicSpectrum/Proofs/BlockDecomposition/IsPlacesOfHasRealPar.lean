import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemSchwartzAOfIsMonoFock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM

theorem isPlaces_of_hasRealPar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (l : D.what₂.Tau → ℝ), IsCharAF D.host.F ψ → IsInfFam θ → HasRealPar ψ θ l → PositivityTheory.SiegelWeilFormula.Gen.IsPlaces D.sp.cm.sig ψ θ l ∧ Nonempty D.what₂.Tau := by
  intro D ψ θ l hψ hθ hl
  refine ⟨⟨fun τ => GlobalTheory.Mem.VolExists.infEmb_continuous (hθ τ),
    GlobalTheory.Mem.VolExists.infEmb_bijective (isCMExt_host D) (GlobalTheory.Mem.Vol.isCMFam_host _ D.host _ D.eTau) hθ,
    fun τ z => GlobalTheory.Mem.VolExists.infEmb_sigR (isCMExt_host D) (hθ τ) z,
    fun τ => GlobalTheory.CompanionTheory.IfrAdd.realPar_ne_zero hψ hθ hl τ, hl⟩, ?_⟩
  exact D.eTau.nonempty_congr.2 inferInstance

end GlobalTheory.CompanionTheory.MM
