import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicBetaCompactInduction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRowM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCompactSubgroupSmallAnnihilator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSetFiniteCosetRepresentatives

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.CompanionTheory.BZBeta
open scoped Topology

namespace GlobalTheory.CompanionTheory.BZOnto

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem betaFun_add (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (n + 1)) V) (x y : V) (g : Mir k (n + 1)) :
    betaFun ψ τ (x + y) g = betaFun ψ τ x g + betaFun ψ τ y g := by
  simp only [betaFun, map_add, Submodule.Quotient.mk_add]

theorem betaFun_smul (ψ : AddChar k Circle) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (n + 1)) V) (c : ℂ) (x : V) (g : Mir k (n + 1)) :
    betaFun ψ τ (c • x) g = c • betaFun ψ τ x g := by
  simp only [betaFun, map_smul, Submodule.Quotient.mk_smul]

end GlobalTheory.CompanionTheory.BZOnto

end
