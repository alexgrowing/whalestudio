import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
import ReciprocityTheory.AnalyticForms.PotentialTheory.LogInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.GreenOfPoincareLelongHyperplane
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsCompatChartRestrOpen

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

def PLLocalStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (L : LocPot X) (s : X → X → ℂ) {r : ℕ} (m : Fin r → ℕ)
    (W : Fin r → Set X) (B : ∀ k, FinHolAtlas e (W k)),
    IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ k, HoloMap (B k) A Subtype.val) →
    ∀ (ψ : OpenPartialHomeomorph X (Fin (e + 1) → ℂ)), IsCompatChart A ψ →
    ∀ v : X → ℝ, A.Smooth v → tsupport v ⊆ ψ.source → ∀ Φ : Fin e → LocPot X,
      (∀ i, IsPotential A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun v) Φ) (logNormSec L s) =
        ∑ k, (m k : ℝ) * mInt (B k) (fun i => (Φ i).pullback Subtype.val continuous_subtype_val)
            (v ∘ Subtype.val) - mInt A (Fin.cons L Φ) v

theorem poincareLelong : PoincareLelongStatement := PLAux.pl_global

end

end ReciprocityTheory.AnForm.M
