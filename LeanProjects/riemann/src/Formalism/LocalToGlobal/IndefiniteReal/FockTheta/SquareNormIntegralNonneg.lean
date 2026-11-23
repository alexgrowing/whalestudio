import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjInvOfReal
import Formalism.PeriodIntegrals.HookBound

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix MeasureTheory

namespace Formalism.IndefR.Fock.Delta

open Formalism.IndefR.Fock.Sk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def factProd {D : D7} (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) : ℝ :=
  ∏ τ, ((∏ i ∈ Finset.range (p τ), ((ap τ i).factorial : ℝ)) * ∏ i ∈ Finset.range (q τ), ((am τ i).factorial : ℝ))

def FockDeltaLow (D : D7) : Prop :=
  ∀ (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ),
    (∀ τ, p τ + q τ ≤ m) → (∀ τ, p τ ≤ n ∧ q τ ≤ n) → (∀ τ, Antitone (ap τ) ∧ Antitone (am τ)) →
    (∀ τ i, p τ ≤ i → ap τ i = 0) → (∀ τ i, q τ ≤ i → am τ i = 0) →
      factProd p q ap am ≤ (Formalism.REAL.fockF (delta (D := D) (m := m) (n := n) p q ap am) (delta p q ap am)).re

def NormDeltaLow (D : D7) : Prop :=
  LineAtExists D →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ),
    PairSetup ψ θ S T sS sT BS BT pS pT →
    ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 →
      ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) →
        ∀ (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ),
          (∀ τ, p τ + q τ ≤ T.rank) → (∀ τ, p τ ≤ S.rank ∧ q τ ≤ S.rank) → (∀ τ, Antitone (ap τ) ∧ Antitone (am τ)) →
          (∀ τ i, p τ ≤ i → ap τ i = 0) → (∀ τ i, q τ ≤ i → am τ i = 0) →
            factProd p q ap am * nrm2 μ 𝓕 f ≤
              nrm2 μ 𝓕 (fockVec (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT (delta p q ap am) f)

end Formalism.IndefR.Fock.Delta

end
