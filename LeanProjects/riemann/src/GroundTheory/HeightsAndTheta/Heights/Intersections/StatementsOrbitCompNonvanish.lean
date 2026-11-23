import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def OrbitCompNonvanish.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (E : MRing ι),
    IsMultiHomogIdeal P → E ∉ P →
    ∃ (D : MRing ι) (a : K → ℕ), IsMultiHomog D a ∧ D ∉ P ∧
      ∀ z : (Σ k, ι k) → ℂ, eval z (map (Int.castRingHom ℂ) D) ≠ 0 →
        ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) E) ≠ 0

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
