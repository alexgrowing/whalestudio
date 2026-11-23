import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerLast
import GroundTheory.HeightsAndTheta.Heights.Intersections.FunFieldLeLocRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityValuationCentre.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsMultiProjPrime P → ∀ (Γ : Type) [LinearOrderedCommGroupWithZero Γ] (v : Valuation (funField P) Γ) (n : ℤ),
    v (n : funField P) < 1 →
    ∃ W : Ideal (MRing ι), IsMultiProjPrime W ∧ P ≤ W ∧ C n ∈ W ∧
      ∀ z : funField P, (z : FractionRing (MRing ι ⧸ P)) ∈ locRing P W → v z ≤ 1

theorem RegularityValuationCentre.exists_int_valuation_lt_one {F : Type*} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ∃ n : ℤ, n ≠ 0 ∧ v.valuation F (n : F) < 1 := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hc : v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx0 hxv (Algebra.IsIntegral.isIntegral x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  refine ⟨n, hn0, ?_⟩
  have e : (n : F) = algebraMap (NumberField.RingOfIntegers F) F (algebraMap ℤ _ n) := by simp
  rw [e, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact hn

end

end GroundTheory.Heights₂.Heights.Inter
