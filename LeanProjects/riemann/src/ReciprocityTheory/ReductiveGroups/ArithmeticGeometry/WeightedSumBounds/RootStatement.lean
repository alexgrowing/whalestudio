import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants

namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh

noncomputable section

def RootStatement : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h m : ℕ) (ty : Fin d → ZMod h) (i : ZMod h) (G : LogFGL v d)
      (γ : Fin m → Fin d → PowerSeries C), (∀ u, IsCurve v (γ u)) →
      (∀ u, G.IsOfType p ty i (γ u)) → ∀ (n j : ℕ), 1 ≤ n →
      ∀ (V : Type) [AddCommGroup V] [Module C V] (La : (Fin d → C) →ₗ[C] V),
        Module.finrank C (Submodule.span C (Set.range fun u => La (G.lc p (γ u) n))) ≤ j →
        ∃ x : Matrix (Fin m) (Fin m) C, (∀ w u, IsIntV v (x w u)) ∧ v x.det = 0 ∧
          let γ' : Fin m → Fin d → PowerSeries C :=
            fun w => G.sumF fun u => rescaleCurve (x w u) (γ u)
          (∀ w, tangent (γ' w) = ∑ u, x w u • tangent (γ u)) ∧
          (∀ w, G.IsOfType p ty i (γ' w)) ∧
          ∀ w : Fin m, j ≤ w.val → La (G.lc p (γ' w) n) = 0

def LowAStatement : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → 3 ≤ p → v (p : C) = 1 → ∀ (d h : ℕ), 0 < h → Even h →
      ∀ (ty : Fin d → ZMod h) (G : LogFGL v d), MuAction G p h ty → ∀ (j K : ℕ),
        (∀ i : ZMod h, Odd i.val → (Finset.univ.filter fun a => ty a = i).card ≤ j) →
        ∃ (γ : Fin d → Fin d → PowerSeries C) (dp : Fin d → ℤ), IsBasis G p ty γ ∧
          (∀ a, -1 ≤ dp a ∧ dp a ≤ K) ∧ (∀ a, Odd (ty a).val → dp a = -1) ∧
          (∀ i : ZMod h, Even i.val →
            (Finset.univ.filter fun a => ty a = i ∧ dp a < K).card ≤ (K + 1) * j) ∧
          ∀ a, 0 ≤ dp a → G.lc p (γ a) 1 = 0 ∧
            G.lc p (γ a) 2 ∈ Submodule.span C
              (Set.range fun b : {b // dp a - 1 ≤ dp b} => tangent (γ b.1))

end

end ReciprocityTheory.ChartRestriction.G.Sh
