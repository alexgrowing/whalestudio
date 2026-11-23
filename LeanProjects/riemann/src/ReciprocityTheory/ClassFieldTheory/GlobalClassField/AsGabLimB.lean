import ReciprocityTheory.ClassFieldTheory.GlobalClassField.AsGabLim

namespace ReciprocityTheory.DiscreteGroups.GlobalClassField

open _root_.Neutral.B1 Topology Function

variable {F : Type*} [Field F] {L : IntermediateField F (AlgebraicClosure F)}

theorem isOpen_fiber_of_isOpen_ker {A B : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [Group B]
    (φ : A →* B) (h : IsOpen (φ.ker : Set A)) (b : B) : IsOpen {a | φ a = b} := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  have ha' : φ a = b := ha
  have hO : IsOpen ((fun y : A => a⁻¹ * y) ⁻¹' (φ.ker : Set A)) := h.preimage (continuous_const.mul continuous_id)
  refine Filter.mem_of_superset (hO.mem_nhds ?_) ?_
  · show a⁻¹ * a ∈ φ.ker
    rw [inv_mul_cancel]; exact one_mem _
  · intro y hy
    have hy' : φ (a⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hy'
    exact hy'.symm.trans ha'

theorem isOpen_ker_abRestrict (h : IsFiniteAbelian F L) :
    IsOpen ((abRestrict F L h).ker : Set (Field.absoluteGaloisGroupAbelianization F)) := by
  have := h.finiteDimensional
  have hq : IsOpen ((toAb F) ⁻¹' ((abRestrict F L h).ker : Set (Field.absoluteGaloisGroupAbelianization F))) := by
    have e : (toAb F) ⁻¹' ((abRestrict F L h).ker : Set (Field.absoluteGaloisGroupAbelianization F)) =
        ((L.fixingSubgroup : Subgroup Gal(AlgebraicClosure F/F)) : Set Gal(AlgebraicClosure F/F)) := by
      ext g
      exact abRestrict_toAb_eq_one_iff h g
    rw [e]
    exact L.fixingSubgroup_isOpen
  exact ((QuotientGroup.isQuotientMap_mk _).isOpen_preimage).1 hq

theorem isOpen_abRestrict_fiber (h : IsFiniteAbelian F L) (τ : L ≃ₐ[F] L) :
    IsOpen {x : Field.absoluteGaloisGroupAbelianization F | abRestrict F L h x = τ} :=
  isOpen_fiber_of_isOpen_ker _ (isOpen_ker_abRestrict h) τ

end ReciprocityTheory.DiscreteGroups.GlobalClassField
