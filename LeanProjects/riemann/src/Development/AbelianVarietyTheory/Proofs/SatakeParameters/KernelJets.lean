import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.KernelAwayPrimes

noncomputable section

namespace GlobalTheory.LiftTypePrime

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

def StdAt (D : D7) (g : ℕ) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∃ L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E), (∀ x, x ∈ L₀ ↔ ∀ k, IsIntegral ℤ (x k)) ∧ EqAt D g L L₀

open Classical in

def typeWt (D : D7) (N N' : ℕ) : Idx D N N' → (D.what₂.Tau → ℕ) := fun k => Pi.single k.1 1

def inLetters (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) :
    MvPolynomial (Idx D N N') ℂ →ₐ[ℂ] MvPolynomial (Idx D N N') ℂ :=
  MvPolynomial.aeval fun k => MvPolynomial.C (s k.1) * MvPolynomial.X k

def KernelJets (D : D7) (X : ErrX D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  InducedCMType D → HostFieldConditions D →
  ∀ (ig : Fin 2), FamTie D ig cc δ e →
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p = D.host.g ig →
  ∀ (S : Finset ℕ), D.host.g ig ∉ S →
  ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' → StdAt D (D.host.g ig) L → StdAt D (D.host.g ig) L' →
  ∀ (s : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D s →
  ∀ (Θ : VC D N N' → ℂ), IsKerG X ig cc δ e S L L' Θ →
  ∀ (P : MvPolynomial (Idx D N N') ℂ) (dg : D.what₂.Tau → ℕ), (∀ m, IntAt lam (P.coeff m)) →
    P.IsWeightedHomogeneous (typeWt D N N') dg → (∑ τ, dg τ) + 1 < D.host.g ig →
    IntAt lam ((D.host.g ig : ℂ) ^ (D.R.f * N * N') *
      (∏ τ, embT D τ (D.host.conj ((X.piG ig : 𝓞 D.host.E) : D.host.E)) ^ dg τ) *
      applyAt0 D (inLetters D s P) Θ)

end GlobalTheory.LiftTypePrime

end
