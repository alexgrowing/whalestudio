import Formalism.HermitianCurvature.LemmaDensOfSteps

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

theorem inner_density_of_averaging : Formalism.FourierDecayAlt.DensityAveraging.DensStepJOfAvg := by
  rintro ⟨C0, hI⟩ hAvg
  refine ⟨C0, ?_⟩
  intro CV hCV k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ H hrel hG hc hMore
  obtain ⟨S, hS⟩ := hI CV hCV k r Wp Wq D A ε mm F' γ H hrel hG hc
  obtain ⟨C', x₁, hb⟩ := hS hMore
  exact S.tie (hAvg S.β S.β_ne S.V S.p S.s S.w S.a C' x₁ S.w_inj hb S.k₀)

theorem top_density_of_averaging : Formalism.FourierDecayAlt.DensityAveraging.DensStepTopOfAvg := by
  rintro ⟨C0, hI⟩ hAvg
  refine ⟨C0, ?_⟩
  intro CV hCV k r Wp Wq _ _ _ _ _ _ D A ε mm F' γ H hrel hG hc hMore
  obtain ⟨S, hS⟩ := hI CV hCV k r Wp Wq D A ε mm F' γ H hrel hG hc
  obtain ⟨C', x₁, hb⟩ := hS hMore
  exact S.tie (hAvg S.β S.β_ne S.V S.p S.s S.w S.a C' x₁ S.w_inj hb S.k₀)

def averagingDatumInhabited {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) (F' : B.Mat k r → (Wq →L[ℂ] Wp)) (γ : B.Mat k r) : Formalism.FourierDecayAlt.DensityAveraging.AvgDatum D F' γ where
  V := ℂ
  p := normSeminorm ℂ ℂ
  β := 1
  β_ne := one_ne_zero
  s := 1
  w := fun _ => 0
  w_inj := fun i j _ => Subsingleton.elim i j
  a := fun _ => 1
  k₀ := 0
  tie := fun h => absurd h (by simp)

end Formalism.FourierDecayAlt.P
