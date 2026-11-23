import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
import ReciprocityTheory.AnalyticForms.LeviForms.PullDominateStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt

namespace ReciprocityTheory.AnForm.P

open MeasureTheory ReciprocityTheory.AnForm.M FinHolAtlas

noncomputable section

def UnifRestrictStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ)
    (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s →
    ∀ (L' : LocPot X) (v : X → X → ℂ) (Dg : Set X), IsPotential A L' → IsSection A L' v →
      IsSNC A L' v ![1] ![Dg] →
      IsSNC A (L + L') (fun x y => s x y * v x y) (Fin.snoc m 1) (Fin.snoc W Dg) →
      ∃ (B : FinHolAtlas e Dg) (hB : HoloMap B A Subtype.val) (n' : ℕ) (m' : Fin n' → ℕ)
        (W' : Fin n' → Set Dg),
        IsPotential B (Θ.pullback Subtype.val hB.1) ∧ IsPosPot B (Θ.pullback Subtype.val hB.1) ∧
          IsSNC B (L.pullback Subtype.val hB.1) (fun x y => s x.1 y.1) m' W'

def UnifExpandStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (L' : LocPot X) (v : X → X → ℂ) (Dg : Set X)
    (B : FinHolAtlas e Dg), IsPotential A L' → IsSection A L' v → IsSNC A L' v ![1] ![Dg] →
    HoloMap B A Subtype.val → ∀ (P : LocPot X) (u : X → ℝ) (Φ : Fin e → LocPot X),
      IsPotential A P → A.Smooth u → (∀ i, IsPotential A (Φ i)) →
        mInt A (Fin.cons (P + LocPot.ofFun u) Φ) (fun y => -logNormSec L' v y) =
          mInt A (Fin.cons P Φ) (fun y => -logNormSec L' v y) -
            mInt B (fun i => (Φ i).pullback Subtype.val continuous_subtype_val) (u ∘ Subtype.val) +
            mInt A (Fin.cons L' Φ) u

theorem mInt_neg_integrand {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (g : X → ℝ) : mInt A Φ (fun y => -g y) = -mInt A Φ g := by
  unfold mInt
  split_ifs
  · simp only [integralWith, mul_neg, neg_mul, integral_neg, Finset.sum_neg_distrib]
  · simp

end

end ReciprocityTheory.AnForm.P
