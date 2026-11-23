import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open scoped ComplexOrder

namespace GlobalTheory.Mean4

theorem antisym_of_eventually :
    ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (Φ : ℝ → Fn Y) (hh : Fn Y), LimFam Φ → (∀ B : ℝ, 2 ≤ B → ∀ᶠ R in atTop, ∀ (τ : D.what₂.Tau) (a b : Fin Y.N), (b : ℕ) = a + 1 → (b : ℕ) ≠ Y.j → ∀ u : Wt Y, Y.arDeg (setB Y B) R (linRoot u ^ (dimFl D.what₂.Tau Y.N + 1)) + Y.arDeg (setB Y B) R (linRoot (fun σ i => u (swapAt τ a b (σ, i)).1 (swapAt τ a b (σ, i)).2) ^ (dimFl D.what₂.Tau Y.N + 1)) = Y.vol * (atWt Y hh u + atWt Y hh (fun σ i => u (swapAt τ a b (σ, i)).1 (swapAt τ a b (σ, i)).2))) → Antisym Φ hh := by
  intro D Y Φ hh hlim hev B hB τ a b hab hj u
  have h1 := ((hlim B hB) (linRoot u ^ (dimFl D.what₂.Tau Y.N + 1))).add
    ((hlim B hB) (linRoot (fun σ i => u (swapAt τ a b (σ, i)).1 (swapAt τ a b (σ, i)).2) ^
      (dimFl D.what₂.Tau Y.N + 1)))
  have h2 := tendsto_nhds_unique_of_eventuallyEq h1
    (tendsto_const_nhds (x := Y.vol * (atWt Y hh u +
      atWt Y hh (fun σ i => u (swapAt τ a b (σ, i)).1 (swapAt τ a b (σ, i)).2))))
    ((hev B hB).mono fun R hR => hR τ a b hab hj u)
  change atWt Y (Φ B) u + atWt Y (Φ B) (fun σ i => u (swapAt τ a b (σ, i)).1 (swapAt τ a b (σ, i)).2) = _ at h2
  linarith

end GlobalTheory.Mean4
