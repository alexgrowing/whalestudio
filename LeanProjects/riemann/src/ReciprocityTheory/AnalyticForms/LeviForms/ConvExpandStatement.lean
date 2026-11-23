import ReciprocityTheory.AnalyticForms.LeviForms.TailBound
import ReciprocityTheory.AnalyticForms.LeviForms.MixedIntegralInclusionExclusion
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasure
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

def ConvTailStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ}
    (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L →
    IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) →
    ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ),
      (∀ i, IsSingWeight A L s (th i) (ph i) C₅) →
      (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) →
      (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) →
      ∃ K : ℝ, ∀ R : ℝ, Real.exp 1 ≤ R →
        (∀ t, 0 < t → t ≤ t₀ →
          ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y))
              ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ) ≤
            ENNReal.ofReal (K * Real.log R ^ 2 / R)) ∧
        ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y))
            ∂maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) ≤
          ENNReal.ofReal (K * Real.log R ^ 2 / R)

def ConvDensStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ : LocPot X)
    (s : X → X → ℂ) (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ),
    IsClosed (bdry s) → IsPotential A Θ → (∀ i, IsPotential A (th i)) → (∀ i, A.SmoothOn (bdry s)ᶜ (ph i)) →
    (∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ i, A.Smooth (phT i t)) →
    (∀ i, IsRegFamilyC2 A s (ph i) (phT i)) →
      ∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (bdry s)ᶜ, IsCompact K →
        TendstoUniformlyOn (fun t => locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j)
          (locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j) (nhdsWithin 0 (Set.Ioi 0)) K

theorem conv_dens : ConvDensStatement := by
  intro e X _ A Θ s th ph phT hB hΘ hth hph hT hC2 j K hK hKc
  exact conv_dens_of_closed A Θ s th ph phT hB hΘ hth hph hT hC2 j K hK hKc

def ConvExpandStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (P : Fin e → LocPot X), IsPotential A Θ → (∀ i, IsPotential A (P i)) →
    ∀ g : X → ℝ, Continuous g →
      mInt A (fun i => P i + Θ.rsmul (-1)) g =
        ∑ S : Finset (Fin e), (-1 : ℝ) ^ (e - S.card) *
          mInt A (fun i => if i ∈ S then P i else Θ) g

end

end ReciprocityTheory.AnForm.P
