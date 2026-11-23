import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BejjSmulLeft
import Formalism.MahlerMeasure.MahlerMeasureProofs.MeanGam
import Formalism.MahlerMeasure.CoarseLevelSlackInequalities
import Formalism.MahlerMeasure.FinalD

noncomputable section

namespace Formalism.MainNotions.G.GramWindowAlt

open MvPolynomial Finset

def GramWindow2 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (n del h Y0 : ℕ) (k : ℤ) (La0 : ℝ) (t0 : ℕ)
    (Ψ : ℕ → MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p]) (e : Fin n → MvPolynomial σ ℚ_[p])
    (s : ℕ → ℚ_[p]) (c : Fin n → Fin n → ℕ → ℚ_[p]),
    LinearIndependent ℤ_[p] e →
    (∀ j (a : ℚ_[p]) u v, Ψ j (a • u) v = a * Ψ j u v) → (∀ j u u' v, Ψ j (u + u') v = Ψ j u v + Ψ j u' v) →
    (∀ j (a : ℚ_[p]) u v, Ψ j u (a • v) = a * Ψ j u v) → (∀ j u v v', Ψ j u (v + v') = Ψ j u v + Ψ j u v') →
    0 < Y0 → Y0 ≤ p ^ h → del + 1 ≤ p ^ h → 0 ≤ k → (∀ a b i, ‖c a b i‖ ≤ 1) →
    (Formalism.GM.binMatK ℚ_[p] del c).det ≠ 0 →
    -Real.logb p ‖(Formalism.GM.binMatK ℚ_[p] del c).det.leadingCoeff‖ +
        ((Formalism.GM.binMatK ℚ_[p] del c).det.natDegree : ℝ) / ((p : ℝ) - 1) ≤ (n : ℝ) * La0 →
    (∀ j ∈ Finset.range Y0, s j ≠ 0 ∧ ‖s j‖ ≤ 1 ∧ ∀ a b,
      s j * Ψ j (e a) (e b) =
        ((Formalism.GM.binMatK ℚ_[p] del c).map (Polynomial.eval (((t0 + j : ℕ) : ℚ_[p])))) a b) →
    (∑ j ∈ Finset.range Y0, (Formalism.GM.M.bad p (Ψ j) (Submodule.span ℤ_[p] (Set.range e)) k : ℝ)) ≤
      (Y0 : ℝ) * ((n : ℝ) * ((del : ℝ) / Y0 + (La0 + (del : ℝ) * h / Y0) / ((k : ℝ) + 1)))

end Formalism.MainNotions.G.GramWindowAlt

end
