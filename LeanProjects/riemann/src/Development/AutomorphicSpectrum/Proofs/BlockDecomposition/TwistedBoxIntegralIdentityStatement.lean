import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedBoxIntegralIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_box_integral_vanishing : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ), Continuous ψ → HasConductor ψ c → ∀ (m : ℕ) (t : kˣ) (M : Set (Fin m → k)) (f : (Fin m → k) → ℂ) (A : ℂ), IsCompact M → MeasurableSet M → Continuous f → (∀ b ∈ box m (c * t⁻¹), ∫ x in M, ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * f x ∂(piHaar ν m) = A) → ∫ x in M ∩ (box m t : Set (Fin m → k)), f x ∂(piHaar ν m) = A := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.setIntegral_inter_box_of_twists | exact GlobalTheory.CompanionTheory.MirPair.setIntegral_inter_box_of_twists | (intros; apply GlobalTheory.CompanionTheory.MirPair.setIntegral_inter_box_of_twists <;> assumption)
