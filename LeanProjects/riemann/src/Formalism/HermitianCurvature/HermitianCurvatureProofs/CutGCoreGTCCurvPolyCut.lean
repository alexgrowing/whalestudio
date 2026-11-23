import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCCurvCut

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def sumU (P : M.Par) : ℂ := ∑ i ∈ Finset.Icc 1 P.k, ((P.u i : ℂ) + (P.u' i : ℂ))

def GTCCurvScal : Prop :=
  ∀ (P : M.Par), 2 ≤ P.k → ∀ ρ : M.Ty P,
    (∃ c : ℕ → ℂ, ∀ u : ℂ, M.wC P ρ u = u ^ (P.k + 1) * (-(P.TT : ℂ)) +
        u ^ P.k * ((P.TT : ℂ) * ((absTy P ρ : ℂ) - 1 - sumU P)) + ∑ i ∈ Finset.range P.k, u ^ i * c i) ∧
    (∃ c : ℕ → ℂ, ∀ u : ℂ, M.xC P ρ u = u ^ (P.k - 1) + (absTy P ρ : ℂ) * u ^ (P.k - 2) +
        ∑ i ∈ Finset.range (P.k - 2), u ^ i * c i) ∧
    (∀ ex : Finset ℕ, (∃ l ∈ ex, l ∈ Finset.Icc 1 (P.k - 1)) →
      ∃ c : ℕ → ℂ, ∀ u : ℂ, M.xEx P ex ρ u = ∑ i ∈ Finset.range (P.k - 1), u ^ i * c i)

def GTCCurvPolyOfScal : Prop := GTCCurvScal → GTCCurvPoly

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
