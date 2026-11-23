import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCharacterBilinearLawsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountableMatricesAndCosetsStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem dsum_stronglyMeasurable : ∀ {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (Φ : Mx D ρ p → ℂ), StronglyMeasurable Φ → (∀ y, Summable (fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y)‖)) → StronglyMeasurable (fun v : Mx D ρ p × Mx D ρ p => GlobalTheory.CompanionTheory.FJE.dsum ψ b₀ Φ v.2 v.1) := by
  intro D ρ p ψ hψ b₀ Φ hΦ hs
  haveI := (GlobalTheory.T.countable_matrices_and_cosets D ρ p).1
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  obtain ⟨_, _, _, _, _, hc⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws ψ hψ b₀
  have hterm : ∀ ξ : Matrix (Fin ρ) (Fin p) D.host.E, Measurable fun v : Mx D ρ p × Mx D ρ p =>
      GlobalTheory.CompanionTheory.FJE.chv ψ b₀ v.2 (GlobalTheory.CompanionTheory.FJE.rt ξ) * Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + v.1) := by
    intro ξ
    have h1 : Measurable fun y : Mx D ρ p => GlobalTheory.CompanionTheory.FJE.chv ψ b₀ y (GlobalTheory.CompanionTheory.FJE.rt ξ) :=
      (hc.comp (continuous_id.prodMk continuous_const)).measurable
    have h2 : Measurable fun y : Mx D ρ p => Φ (GlobalTheory.CompanionTheory.FJE.rt ξ + y) :=
      hΦ.measurable.comp (continuous_const_add (GlobalTheory.CompanionTheory.FJE.rt ξ)).measurable
    exact (h1.comp measurable_snd).mul (h2.comp measurable_fst)
  exact (Measurable.tsum hterm).stronglyMeasurable

end GlobalTheory.CompanionTheory.FJE
