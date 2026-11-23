import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelJets

noncomputable section

namespace GlobalTheory.LiftTypePrime

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

def TranslateJets (D : D7) (X : ErrX D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  InducedCMType D → HostFieldConditions D →
  ∀ (ig : Fin 2), FamTie D ig cc δ e →
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p = D.host.g ig →
  ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' → StdAt D (D.host.g ig) L → StdAt D (D.host.g ig) L' →
  ∀ (s : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D s →
  ∀ (t y : VC D N N'), TorsPrime D (D.host.g ig) (La D (tor0 D cc δ) L L') t →
    D.host.φ₀ ((X.piG ig : 𝓞 D.host.E) : D.host.E) • y ∈ La D (tor0 D cc δ) L L' →
  ∀ (P : MvPolynomial (Idx D N N') ℂ) (dg : D.what₂.Tau → ℕ), (∀ m, IntAt lam (P.coeff m)) →
    P.IsWeightedHomogeneous (typeWt D N N') dg → (∑ τ, dg τ) + 1 < D.host.g ig →
    IntAt lam ((∏ τ, embT D τ (D.host.conj ((X.piG ig : 𝓞 D.host.E) : D.host.E)) ^ dg τ) *
      applyAt0 D (inLetters D s P) (U D (tor0 D cc δ) (t + y) (e N N' L L')))

end GlobalTheory.LiftTypePrime

end
