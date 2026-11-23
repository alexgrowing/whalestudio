import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField
open GlobalTheory.Chain

namespace GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def signCard (S : SPar) (b : Bool) : ℕ := (S.filter fun x => x.2 = b).card

def SigLowered (S : D.what₂.Tau → SPar) (i : ℕ) (V' : HSp D) : Prop :=
  ∀ τ, ∃ p' q' : ℕ, p' + i = signCard (S τ) true ∧ q' + i = signCard (S τ) false ∧
    Formalism.UG.HasSignature (gramAt D V' τ) p' q'

def LowVanish (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (i : ℕ) (V' W : HSp D) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    1 ≤ i → SigLowered (parB (Ptw D) k) i V' →
    ∀ ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ), IsStepWeil k ψ V' W ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ (J : Set (GA D W)) (χ : GA D W → ℂ), ∀ F ∈ MultT θ M' J χ, ∀ (v : SmT M') (f' : WO V' W → ℂ),
      IsThetaFunO ψ V' W f' → Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) = 0

def LowVanishConv (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (i : ℕ) (V' W : HSp D) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    1 ≤ i → SigLowered (parB (Ptw D) k) i V' →
    ∀ ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ), IsStepWeil k ψ V' W ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ (J : Set (GA D W)) (χ : GA D W → ℂ), ∀ F ∈ MultT θ M' J χ, ∀ (v : SmT M') (f' : WO V' W → ℂ),
      IsThetaFunO ψ V' W f' → ∀ g, IntegrableOn (fun h => thetaKO ω' g h f' * F v h) 𝓕 ν ∧
        ∫ h in 𝓕, thetaKO ω' g h f' * F v h ∂ν = 0

theorem signCard_dualPar (S : SPar) (b : Bool) : signCard (dualPar S) b = signCard S b := by
  unfold signCard dualPar
  rw [Finset.filter_image, Finset.card_image_of_injective]
  intro x y h
  simp only [Prod.mk.injEq, neg_inj] at h
  exact Prod.ext h.1 h.2

example : signCard {((5 : ℚ), true), (3, false), (-4, true)} true = 2 := by decide +kernel

end GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing

end
