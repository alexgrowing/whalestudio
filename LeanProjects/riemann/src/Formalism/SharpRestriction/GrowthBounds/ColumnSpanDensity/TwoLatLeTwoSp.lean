import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.DeltaPsiH
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem letterWt_anti (m d : ℕ) (b : Bool) : Antitone (letterWt m d b) := by
  intro i j hij
  cases b
  · simp only [letterWt, Bool.false_eq_true, if_false]
    by_cases hi : i = Fin.last m
    · have hj : j = Fin.last m := le_antisymm (Fin.le_last j) (hi ▸ hij)
      simp [hi, hj]
    · simp only [hi, if_false]
      split_ifs <;> omega
  · simp only [letterWt, if_true]
    by_cases hj : j = 0
    · have hi : i = 0 := le_antisymm (hj ▸ hij) (Fin.zero_le i)
      simp [hj, hi]
    · simp only [hj, if_false]
      split_ifs <;> omega

theorem twoLat_le_twoSp {O Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m P Q : ℕ)
    (Λ : Submodule O (Fin (m + 1) → Kf)) (hΛ : IsLattice O Λ) :
    ∀ x ∈ twoLat O m P Q Λ, x ∈ twoSp Kf m P Q := by
  obtain ⟨g, hg, hΛg⟩ := hΛ
  have hsub : ∀ b : Bool, ∀ F ∈ H0 O m (letterWt m (if b then P else Q) b) Λ,
      F ∈ dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m (if b then P else Q) b)) := by
    intro b F hF
    have hle := H0_le_twisted_nabla (O := O) m _ (letterWt_anti m (if b then P else Q) b) g hg
    rw [← hΛg] at hle
    exact la_nablaLTw_le m _ g hg F (hle hF)
  intro x hx
  unfold twoLat tensorLat at hx
  unfold twoSp tensorLat
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, hF, rfl⟩ := hy
    exact Submodule.subset_span ⟨F, fun b => hsub b (F b) (hF b), rfl⟩
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul c y _ hy => exact Submodule.smul_of_tower_mem _ c hy

end Formalism.MainNotions.flipOneThree.Pf

end
