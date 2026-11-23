import Mathlib
import ReciprocityTheory.NeutralLocalFields.Reciprocity

namespace ReciprocityTheory.DiscreteGroups.GlobalClassField

open _root_.Neutral.B1 Topology Function
open scoped commutatorElement

variable {F : Type*} [Field F] {L L' : IntermediateField F (AlgebraicClosure F)}

def ResCompat (hle : L ≤ L') (τ' : L' ≃ₐ[F] L') (τ : L ≃ₐ[F] L) : Prop :=
  ∀ x : L, τ' (IntermediateField.inclusion hle x) = IntermediateField.inclusion hle (τ x)

theorem ResCompat.unique {hle : L ≤ L'} {τ' : L' ≃ₐ[F] L'} {τ₁ τ₂ : L ≃ₐ[F] L}
    (h₁ : ResCompat hle τ' τ₁) (h₂ : ResCompat hle τ' τ₂) : τ₁ = τ₂ := by
  ext x
  have := (h₁ x).symm.trans (h₂ x)
  exact congrArg Subtype.val ((IntermediateField.inclusion hle).toRingHom.injective this)

theorem ResCompat.one (hle : L ≤ L') : ResCompat hle 1 1 := fun _ => rfl

theorem ResCompat.mul {hle : L ≤ L'} {σ' τ' : L' ≃ₐ[F] L'} {σ τ : L ≃ₐ[F] L}
    (h₁ : ResCompat hle σ' σ) (h₂ : ResCompat hle τ' τ) : ResCompat hle (σ' * τ') (σ * τ) := by
  intro x
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h₂ x, h₁ (τ x)]

theorem ResCompat.refl (τ : L ≃ₐ[F] L) : ResCompat (le_refl L) τ τ := by
  intro x
  rfl

theorem ResCompat.trans {L'' : IntermediateField F (AlgebraicClosure F)} {h₁ : L ≤ L'} {h₂ : L' ≤ L''}
    {τ'' : L'' ≃ₐ[F] L''} {τ' : L' ≃ₐ[F] L'} {τ : L ≃ₐ[F] L}
    (c₂ : ResCompat h₂ τ'' τ') (c₁ : ResCompat h₁ τ' τ) : ResCompat (h₁.trans h₂) τ'' τ := by
  intro x
  have e : IntermediateField.inclusion (h₁.trans h₂) x =
      IntermediateField.inclusion h₂ (IntermediateField.inclusion h₁ x) := rfl
  rw [e, c₂, c₁]
  rfl

theorem ResCompat.inv {hle : L ≤ L'} {τ' : L' ≃ₐ[F] L'} {τ : L ≃ₐ[F] L}
    (h : ResCompat hle τ' τ) : ResCompat hle τ'⁻¹ τ⁻¹ := by
  intro x
  apply τ'.injective
  rw [h (τ⁻¹ x)]
  show (τ' * τ'⁻¹) _ = IntermediateField.inclusion hle ((τ * τ⁻¹) x)
  rw [mul_inv_cancel, mul_inv_cancel]
  rfl

theorem toAb_surjective : Surjective (toAb F) := QuotientGroup.mk'_surjective _

theorem abRestrict_toAb_eq_one_iff (h : IsFiniteAbelian F L) (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    abRestrict F L h (toAb F g) = 1 ↔ g ∈ L.fixingSubgroup := by
  have := h.isGalois
  rw [abRestrict_mk, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]

theorem isGalois_algebraicClosure [CharZero F] : IsGalois F (AlgebraicClosure F) := ⟨⟩

theorem isFiniteAbelian_of_commutator_le [CharZero F] (hfd : FiniteDimensional F L)
    (hc : commutator (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ≤ L.fixingSubgroup) :
    IsFiniteAbelian F L := by
  have := isGalois_algebraicClosure (F := F)
  have hn : L.fixingSubgroup.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g * n * g⁻¹ = ⁅g, n⁆ * n := by
      rw [commutatorElement_def]; group
    rw [h1]
    exact mul_mem (hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))) hn
  have hG : IsGalois F L := (InfiniteGalois.normal_iff_isGalois L).1 hn
  refine ⟨hfd, hG, fun a b => ?_⟩
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) (AlgebraicClosure F) a
  obtain ⟨k, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) (AlgebraicClosure F) b
  have h2 : ⁅g, k⁆ ∈ (AlgEquiv.restrictNormalHom (F := F) (K₁ := AlgebraicClosure F) L).ker := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top k))
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2

theorem mem_closure_commutator_iff [CharZero F] (g : Field.absoluteGaloisGroup F) :
    g ∈ (commutator (Field.absoluteGaloisGroup F)).topologicalClosure ↔
      ∀ L : IntermediateField F (AlgebraicClosure F), IsFiniteAbelian F L → g ∈ L.fixingSubgroup := by
  have := isGalois_algebraicClosure (F := F)
  constructor
  · intro hg L hL
    have h1 : toAb F g = 1 := (QuotientGroup.eq_one_iff g).2 hg
    exact (abRestrict_toAb_eq_one_iff hL g).1 (by rw [h1, map_one])
  · intro hg
    let C : ClosedSubgroup (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :=
      ⟨(commutator (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)).topologicalClosure,
        Subgroup.isClosed_topologicalClosure _⟩
    have hC : (IntermediateField.fixedField C.1).fixingSubgroup = C.1 :=
      InfiniteGalois.fixingSubgroup_fixedField C
    show g ∈ C.1
    rw [← hC]
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
    have hfd : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
      IntermediateField.adjoin.finiteDimensional hint
    have hle : IntermediateField.adjoin F {x} ≤ IntermediateField.fixedField C.1 :=
      IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 hx)
    have hab : IsFiniteAbelian F (IntermediateField.adjoin F {x}) := by
      refine isFiniteAbelian_of_commutator_le hfd ?_
      refine le_trans ?_ (IntermediateField.fixingSubgroup_le hle)
      rw [hC]
      exact Subgroup.le_topologicalClosure _
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hg _ hab) x
      (IntermediateField.mem_adjoin_simple_self F x)

theorem abRestrict_separates [CharZero F] (x : Field.absoluteGaloisGroupAbelianization F)
    (hx : ∀ (L : IntermediateField F (AlgebraicClosure F)) (h : IsFiniteAbelian F L), abRestrict F L h x = 1) : x = 1 := by
  obtain ⟨g, rfl⟩ := toAb_surjective x
  refine (QuotientGroup.eq_one_iff g).2 ((mem_closure_commutator_iff g).2 fun L hL => ?_)
  exact (abRestrict_toAb_eq_one_iff hL g).1 (hx L hL)

theorem abRestrict_ext [CharZero F] {x y : Field.absoluteGaloisGroupAbelianization F}
    (hxy : ∀ (L : IntermediateField F (AlgebraicClosure F)) (h : IsFiniteAbelian F L),
      abRestrict F L h x = abRestrict F L h y) : x = y := by
  have := abRestrict_separates (x * y⁻¹) fun L h => by rw [map_mul, map_inv, hxy L h, mul_inv_cancel]
  exact mul_inv_eq_one.mp this

end ReciprocityTheory.DiscreteGroups.GlobalClassField
