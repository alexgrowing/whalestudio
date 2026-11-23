import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestriction
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (0 < ρ → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit S S₀ d.e d.i₀) ∧ GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D T.rank ρ = ratMx D T.rank ρ ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart S T d.e y = d.extY T y) ∧ (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart S T d.e' y = d.extX T y) ∧ (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart S S₀ T d.i₀ w = d.ext0 T w) ∧ (∀ μ 𝓕 f x, d.mixS T ψ μ 𝓕 f x = GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res S S₀ T d.e d.i₀ μ 𝓕 (heisO ψ S T (d.extX T x) f)) ∧ (∀ μ 𝓕 f x, d.mixS T ψ μ 𝓕 f x = d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0) ∧ (∀ b, d.nB b ∈ NI S d.e) ∧ ∀ c, d.nC c ∈ NI S d.e := by
  first | exact @GlobalTheory.Bridge.heis_bridge | exact GlobalTheory.Bridge.heis_bridge | (intros; apply GlobalTheory.Bridge.heis_bridge <;> assumption)
