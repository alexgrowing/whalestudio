import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

def PolynomialChartInjective.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (k : ℕ) (t : MvPolynomial σ ℂ) (f : Fin k → MvPolynomial σ ℂ) (w : σ → ℂ),
    k + 1 = Fintype.card σ →
    LinearIndependent ℂ (Fin.cons (fun i ↦ eval w (pderiv i t)) (fun j i ↦ eval w (pderiv i (f j))) :
      Fin (k + 1) → σ → ℂ) →
      ∃ U ∈ 𝓝 w, Set.InjOn (fun z : σ → ℂ ↦ eval z t) {z | z ∈ U ∧ ∀ j, eval z (f j) = 0}

end

end GroundTheory.Heights₂.Heights
