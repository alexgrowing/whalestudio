import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.DegStB

namespace ReciprocityTheory.GeometryOfNumbersTheory

open NumberField Module
open scoped ComplexOrder

variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_isFrame (E : Submodule (𝓞 K) V) (hE : E.FG) :
    ∃ v : Fin (latRank K E) → V, IsFrame K E v := by
  obtain ⟨r, v, hv⟩ := exists_isFullRankFamily_of_fg E hE
  obtain rfl := hv.length_eq_latticeRank
  exact ⟨v, hv⟩

theorem IsFrame.card_eq {E : Submodule (𝓞 K) V} {r : ℕ} {v : Fin r → V} (hv : IsFrame K E v) :
    r = latRank K E := by
  exact hv.length_eq_latticeRank

theorem IsFrame.relIndex_ne_zero {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup ≠ 0 := by
  exact hv.relIndex_span_frame_ne_zero hE

theorem degreeOfFamily_eq_degreeOfFamily (h : HermFam K V) {E : Submodule (𝓞 K) V} (hE : E.FG) {r r' : ℕ}
    {v : Fin r → V} {v' : Fin r' → V} (hv : IsFrame K E v) (hv' : IsFrame K E v') :
    degreeOfFamily h E v = degreeOfFamily h E v' := by
  obtain rfl : r = r' := hv.length_eq_latticeRank.trans hv'.length_eq_latticeRank.symm
  exact degreeOfFamily_eq_of_isFullRankFamily h hE hv hv'

theorem arakelovDegree_eq_degreeOfFamily (h : HermFam K V) {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ}
    {v : Fin r → V} (hv : IsFrame K E v) : deg h E = degreeOfFamily h E v := by
  have hex : ∃ p : (Σ r : ℕ, Fin r → V), IsFrame K E p.2 := ⟨⟨r, v⟩, hv⟩
  unfold deg
  rw [dif_pos hex]
  exact degreeOfFamily_eq_degreeOfFamily h hE hex.choose_spec hv

theorem deg_of_le (h : HermFam K V) {E' E : Submodule (𝓞 K) V} (hE' : E'.FG) (hE : E.FG)
    (hle : E' ≤ E) (hspan : (E : Set V) ⊆ Submodule.span K (E' : Set V)) :
    deg h E' = deg h E -
      Real.log (E'.toAddSubgroup.relIndex E.toAddSubgroup : ℝ) / finrank ℚ K := by
  obtain ⟨v, hv⟩ := exists_isFrame E' hE'
  have hvE : IsFrame K E v := by
    refine ⟨fun i => hle (hv.1 i), hv.2.1, ?_⟩
    intro x hx
    have hx' := hspan hx
    rw [← hv.ds_spanK_eq] at hx'
    exact hx'
  rw [arakelovDegree_eq_degreeOfFamily h hE' hv, arakelovDegree_eq_degreeOfFamily h hE hvE]
  unfold degreeOfFamily
  have hS : Submodule.span (𝓞 K) (Set.range v) ≤ E' :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hv.1)
  have hmul := AddSubgroup.relIndex_mul_relIndex
    (H := (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup) (K := E'.toAddSubgroup)
    (L := E.toAddSubgroup) (fun x hx => hS hx) (fun x hx => hle hx)
  have ha := hv.relIndex_span_frame_ne_zero hE'
  have hc := hvE.relIndex_span_frame_ne_zero hE
  have hb : E'.toAddSubgroup.relIndex E.toAddSubgroup ≠ 0 := fun h0 =>
    hc (by rw [← hmul, h0, mul_zero])
  have hlog : Real.log
      ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup : ℝ) =
      Real.log ((Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E'.toAddSubgroup : ℝ)
        + Real.log (E'.toAddSubgroup.relIndex E.toAddSubgroup : ℝ) := by
    rw [← hmul, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr ha) (Nat.cast_ne_zero.mpr hb)]
  rw [hlog]
  ring

end ReciprocityTheory.GeometryOfNumbersTheory
