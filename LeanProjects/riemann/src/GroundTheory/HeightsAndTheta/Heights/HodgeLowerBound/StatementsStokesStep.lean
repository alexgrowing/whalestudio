import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def stokesMixPot {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A A' : HermLine ι) (n i : ℕ) :
    Fin n → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => if j.val < i then Real.log (A'.h z) else Real.log (A.h z)

def StokesStep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n i : ℕ)
    (A A' : HermLine ι), IsArithVar P (n + 1) → A'.a = A.a → IsSemipositiveH P A → IsSemipositiveH P A' →
    i < n →
      ptsIntegral P (stokesMixPot A A' n (i + 1)) (fun z => Real.log (A'.h z) - Real.log (A.h z)) ≤
        ptsIntegral P (stokesMixPot A A' n i) (fun z => Real.log (A'.h z) - Real.log (A.h z))

end GroundTheory.Heights₂.Heights.LowerBoundFree
