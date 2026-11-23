import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

theorem _root_.GlobalTheory.exists_sum_smul_separating_inertia :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (B : Type) [CommRing B] [MulSemiringAction Γ B]
      (q : Ideal B), q.IsPrime → ∃ (n : ℕ) (c d : Fin n → B) (s : B), s ∉ q ∧ ∀ g : Γ,
        (g ∈ q.inertia Γ → (∑ j, d j * g • c j) - s ∈ q) ∧
        (g ∉ q.inertia Γ → (∑ j, d j * g • c j) ∈ q) := by
  intro Γ _ _ B _ _ q hq
  classical
  haveI := Fintype.ofFinite Γ
  have hmem : ∀ g : Γ, g ∈ q.inertia Γ ↔ ∀ x, g • x - x ∈ q := fun g => Iff.rfl
  have factor : ∀ h : Γ, ∃ x y : B, x + y ∉ q ∧ (h ∉ q.inertia Γ → h • x + y ∈ q) := by
    intro h
    by_cases hh : h ∈ q.inertia Γ
    · exact ⟨1, 0, by simpa using hq.one_notMem, fun h' => (h' hh).elim⟩
    · obtain ⟨x, hx⟩ : ∃ x, h • x - x ∉ q := by simpa [hmem] using hh
      refine ⟨x, -(h • x), fun hm => hx ?_, fun _ => by simp⟩
      rw [← neg_sub]
      exact q.neg_mem (by rwa [sub_eq_add_neg])
  choose x y hxy hzero using factor
  let e := (Fintype.equivFin (Finset Γ)).symm
  have key : ∀ g : Γ, ∑ j, (∏ h ∈ Finset.univ \ e j, y h) * g • ∏ h ∈ e j, x h =
      ∏ h, (g • x h + y h) := by
    intro g
    rw [Finset.prod_add, Finset.powerset_univ,
      Equiv.sum_comp e (fun t => (∏ h ∈ Finset.univ \ t, y h) * g • ∏ h ∈ t, x h)]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.smul_prod', mul_comm]
  refine ⟨Fintype.card (Finset Γ), fun j => ∏ h ∈ e j, x h, fun j => ∏ h ∈ Finset.univ \ e j, y h,
    ∏ h, (x h + y h), ?_, fun g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · intro hs
    obtain ⟨h, -, hh⟩ := Ideal.IsPrime.prod_mem_iff.mp hs
    exact hxy h hh
  · rw [key, ← Ideal.Quotient.eq, map_prod, map_prod]
    refine Finset.prod_congr rfl fun h _ => ?_
    rw [Ideal.Quotient.eq]
    simpa using (hmem g).mp hg (x h)
  · rw [key]
    exact Ideal.IsPrime.prod_mem_iff.mpr ⟨g, Finset.mem_univ g, hzero g hg⟩

end GlobalTheory
