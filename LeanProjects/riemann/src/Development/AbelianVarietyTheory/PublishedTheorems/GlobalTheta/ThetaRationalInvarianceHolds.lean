import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertPrimeOrderParitySignRadicalIntegralForm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilOfVacuum

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped BigOperators

namespace GlobalTheory.Published

def ThetaRationalInvariance : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ N N' : ℕ, Even (N * N') →
    ∀ e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'), ∀ W : WeilO D cc δ N N' e0,
      ∃ a a' : D.what₂.Tau → ℤ,
        (∀ τ, 2 * a τ = W.ep' * W.chV'.n τ - (N' : ℤ)) ∧ (∀ τ, 2 * a' τ = W.ep * W.chV.n τ + (N : ℤ)) ∧
        ∀ (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E)
          (γ' : Matrix (Fin N') (Fin N') D.host.E),
          IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' →
          ∀ F ∈ TT D (tor0 D cc δ) N N',
            W.Om γA γA' F = fun z => (∏ τ, embT D τ γ.det ^ (-(a τ)) * embT D τ γ'.det ^ (-(a' τ))) *
              pull D (tor0 D cc δ) γ γ' F z

theorem thetaRationalInvariance_holds : ThetaRationalInvariance := by
  intro D cc δ hc N N' hN e0 he W
  have h : ∀ (ε n : ℤ) (k : ℕ), (ε = 1 ∨ ε = -1) → Even (n - k) →
      (∃ a, 2 * a = ε * n + k) ∧ ∃ a, 2 * a = ε * n - k := by
    rintro ε n k (rfl | rfl) ⟨j, hj⟩
    · exact ⟨⟨j + k, by omega⟩, ⟨j, by omega⟩⟩
    · exact ⟨⟨-j, by omega⟩, ⟨-j - k, by omega⟩⟩
  choose a' ha' using fun τ => (h _ _ N W.ep_pm.1 (W.chV.par τ)).1
  choose a ha using fun τ => (h _ _ N' W.ep_pm.2 (W.chV'.par τ)).2
  exact ⟨a, a', ha, ha', fun g g' γ γ' hr hr' =>
    GlobalTheory.OddRank.oddEq_of_mem hc hN he W g g' γ γ' a a' hr hr' ha' ha⟩

theorem ThetaRationalInvariance.exists_datum (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (N N' : ℕ)
    (hN : Even N) (hN' : Even N') (e0 : VC D N N' → ℂ) (he : e0 ∈ Th D (tor0 D cc δ) (stdL D N) (stdL D N'))
    (h0 : e0 ≠ 0) (χ : HeckeU D N) (χ' : HeckeU D N') :
    ∃ W : WeilO D cc δ N N' e0, W.chV = χ ∧ W.chV' = χ' := by
  obtain ⟨W, h1, h2, -⟩ := GlobalTheory.FinWeil.exists_weil D cc δ hc N N' hN hN' e0 he h0 χ χ'
  exact ⟨W, h1, h2⟩

end GlobalTheory.Published
