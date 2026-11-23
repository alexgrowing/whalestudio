import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueAdelicMatrixRealComponentsFinitePart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverse
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.RegSch.ChartDer

open GlobalTheory.StdUnn

variable {D : D7}

theorem isUnit_det_map {n : ℕ} {R : Type} [CommRing R] (f : D.host.E →+* R) {T : Matrix (Fin n) (Fin n) D.host.E}
    (hT : IsUnit T.det) : IsUnit (T.map f).det := by
  have := hT.map f
  rwa [RingHom.map_det] at this

theorem isAtTau_iff (θ : InfFam D) (V : HSp D) (τ : D.what₂.Tau) (x : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GA D V) :
    IsAtTau θ V τ x h ↔ compAt θ τ (mt V h) = x ∧ (∀ τ', τ' ≠ τ → compAt θ τ' (mt V h) = 1) ∧
      (mt V h).map (finPart D) = 1 := by
  have : h ∈ GinfC V ↔ (mt V h).map (finPart D) = 1 := by
    rw [GinfC, MonoidHom.mem_ker, Units.ext_iff]
    rfl
  rw [IsAtTau, this]
  exact ⟨fun ⟨a, b, c⟩ => ⟨b, c, a⟩, fun ⟨b, c, a⟩ => ⟨a, b, c⟩⟩

end GlobalTheory.RegSch.ChartDer
