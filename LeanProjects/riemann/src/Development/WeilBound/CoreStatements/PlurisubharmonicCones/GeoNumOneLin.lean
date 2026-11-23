import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace LevelTowerAlt

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem geoNum_one_lin (W : Ideal (MRing J)) :
    ∃ d : K → ℤ, (∀ k, 0 ≤ d k) ∧ ∀ a : K → ℤ, geoNum 1 W (fun _ => a) = ∑ k, a k * d k := by
  classical
  obtain ⟨g0, hg0⟩ : ∃ g0 : Ideal (MRing J) → ℤ, ∀ V b, geoNum 0 V b = g0 V :=
    ⟨fun V => geoNum 0 V (fun i => Fin.elim0 i), fun V b => congrArg _ (Subsingleton.elim _ _)⟩
  have hnn : ∀ V, 0 ≤ g0 V := by
    intro V
    rw [← hg0 V (fun i => Fin.elim0 i)]
    exact dite_nonneg (fun _ => Int.natCast_nonneg _) (fun _ => le_rfl)
  by_cases hW : IsRelevant W
  · refine ⟨fun k => ∑ᶠ V ∈ divSupp W (X ⟨k, (hW k).choose⟩ : MRing J),
        (multAt (W ⊔ Ideal.span {(X ⟨k, (hW k).choose⟩ : MRing J)}) V : ℤ) * g0 V, ?_, ?_⟩
    · intro k
      exact finsum_nonneg fun V => finsum_nonneg fun _ => mul_nonneg (Int.natCast_nonneg _) (hnn V)
    · intro a
      change (if h : IsRelevant W then
          ∑ k, a k * ∑ᶠ V ∈ divSupp W (X ⟨k, (h k).choose⟩ : MRing J),
            (multAt (W ⊔ Ideal.span {(X ⟨k, (h k).choose⟩ : MRing J)}) V : ℤ) *
              geoNum 0 V (Fin.init fun _ : Fin 1 => a)
        else 0) = _
      rw [dif_pos hW]
      simp only [hg0]
  · refine ⟨fun _ => 0, fun _ => le_rfl, fun a => (dif_neg hW).trans ?_⟩
    simp

end LevelTowerAlt
