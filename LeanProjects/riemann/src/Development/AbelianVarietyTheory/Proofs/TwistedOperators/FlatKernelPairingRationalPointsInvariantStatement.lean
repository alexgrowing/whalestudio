import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatKernelPairingRationalPointsInvariant
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.XLastLin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatKernelPairing_rationalPoints_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacL D (σ + 1)) (B : BesL D σ) (s : StFB ψ J B) (vL : VolM D B.L.rank J.W₀.rank) (χ χz : (AE D)ˣ →* Circle) (omz : Om J.W₀ B.L), IsWeilDatumO ψ J.W₀ B.L χ χz omz → ∀ (Φ₀ : WO J.W₀ B.L → ℂ) (Φ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W₀ B.L Φ₀ → IsThetaFunO ψ J.W B.V Φ → ∀ h, (∀ γ ∈ GQ J.W₀, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ ((γ * h₀), B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz ((γ * h₀), 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0) ∧ ∀ γ ∈ GQ B.A, ∀ h₀ h₁, contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb ((γ * h₁), 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 = contractT B.o J.W₀ vL.μ vL.𝓕 (s.om₀ (h₀, B.o.emb (h₁, 1)) (flFB s (s.om (1, h) Φ))) (omz (h₀, 1) Φ₀) 0 := by
  first | exact @GlobalTheory.KerRat.flat_kernel_rat | exact GlobalTheory.KerRat.flat_kernel_rat | (intros; apply GlobalTheory.KerRat.flat_kernel_rat <;> assumption)
