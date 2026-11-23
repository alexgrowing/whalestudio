import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentLowerRowsLeviSetClosedSubgroup

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem levSetInf_closed_subgroup : ∀ (E : Type) [Field E] [NumberField E] (n r : ℕ),
    (∀ g ∈ levSetInf E n r, ∀ h ∈ levSetInf E n r, g * h ∈ levSetInf E n r) ∧
    (∀ g ∈ levSetInf E n r, g⁻¹ ∈ levSetInf E n r) ∧
    (∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin n), u ∈ levSetInf E n r) ∧ IsClosed (levSetInf E n r) := by
  intro E _ _ n r
  refine ⟨fun g hg h hh w => ?_, fun g hg w => ?_, fun u hu => ?_, ?_⟩
  · rw [map_mul]
    exact (levSet_closed_subgroup n r).1 _ (hg w) _ (hh w)
  · rw [map_inv]
    exact (levSet_closed_subgroup n r).2.1 _ (hg w)
  · obtain ⟨h0, h1⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
    exact mem_levSetInf.2 fun i _ => ⟨fun j hj => h0 i j hj, h1 i⟩
  · have hc : ∀ i j : Fin n, Continuous fun g : GL (Fin n) (Cinf E) =>
        (g : Matrix (Fin n) (Fin n) (Cinf E)) i j :=
      fun i j => (Units.continuous_val (M := Matrix (Fin n) (Fin n) (Cinf E))).matrix_elem i j
    have hs : levSetInf E n r = {g : GL (Fin n) (Cinf E) | ∀ i : Fin n, r ≤ (i : ℕ) →
        (∀ j, j < i → (g : Matrix (Fin n) (Fin n) (Cinf E)) i j = 0) ∧
          (g : Matrix (Fin n) (Fin n) (Cinf E)) i i = 1} := Set.ext fun g => mem_levSetInf
    rw [hs]
    simp only [Set.setOf_forall, Set.setOf_and]
    refine isClosed_iInter fun i => isClosed_iInter fun _ => IsClosed.inter ?_ ?_
    · exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (hc i j) continuous_const
    · exact isClosed_eq (hc i i) continuous_const

end GlobalTheory.JSW.MirCinf
