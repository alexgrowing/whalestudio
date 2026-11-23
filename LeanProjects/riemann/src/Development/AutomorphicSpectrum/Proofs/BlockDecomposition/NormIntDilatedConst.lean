import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetIntegralInvMulVec
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientContinuous

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirStable

section Det

variable {k : Type} [Field k]

end Det

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def zM (m : ℕ) (u : kˣ) : Mir k m := levi k m (Matrix.GeneralLinearGroup.scalar (Fin m) u)

section Rep

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def normInt [MeasurableSpace k] (ν : Measure k) (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ)
    (L : Set (Fin n → k)) (v : V) (v' : V') : ℂ :=
  (((piHaar ν n).real L : ℝ) : ℂ)⁻¹ * ∫ x in L, coef T B v v' x ∂(piHaar ν n)

section Int

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

theorem isAddHaar_piHaar (m : ℕ) : (piHaar ν m).IsAddHaarMeasure := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  unfold piHaar
  infer_instance

end Int

section Int

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]

end Int

end Rep

end GlobalTheory.CompanionTheory.MirStable

end
