import Mathlib
import GroundTheory.LocalFields.LocalArtinMap

noncomputable section

namespace GroundTheory.LocalField

open Abstract ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

section Index

theorem index_range_normUnits_of_isAbelianGalois (L : IntermediateField K Ω) [FiniteDimensional K L]
    [IsAbelianGalois K L] : (normUnits K L).range.index = Module.finrank K L := by
  rw [Subgroup.index, ← IsGalois.card_aut_eq_finrank]
  exact (Nat.card_congr (localReciprocityAbelian L).toEquiv).symm

end Index

section Lattice

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem isAbelianGalois_sup (L L' : IntermediateField K Ω) [IsAbelianGalois K L]
    [IsAbelianGalois K L'] : IsAbelianGalois K (L ⊔ L' : IntermediateField K Ω) :=
  isAbelianGalois_of_le_maximalAbelianExtension _
    (sup_le (le_maximalAbelianExtension L) (le_maximalAbelianExtension L'))

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ω] in
theorem mul_comm_of_isAbelianGalois' (L : IntermediateField K Ω) [IsAbelianGalois K L]
    (σ τ : L ≃ₐ[K] L) : σ * τ = τ * σ :=
  mul_comm' σ τ

theorem range_normUnits_le_iff {L L' : IntermediateField K Ω} [FiniteDimensional K L]
    [FiniteDimensional K L'] [IsAbelianGalois K L] [IsAbelianGalois K L'] :
    (normUnits K L).range ≤ (normUnits K L').range ↔ L' ≤ L :=
  range_normUnits_le_range_normUnits_iff (mul_comm_of_isAbelianGalois' L)
    (mul_comm_of_isAbelianGalois' L')

theorem exists_isAbelianGalois_range_normUnits_eq (H : Subgroup Kˣ) [H.FiniteIndex]
    (hH : IsOpen (H : Set Kˣ)) :
    ∃ (L : IntermediateField K Ω) (_ : FiniteDimensional K L) (_ : IsAbelianGalois K L),
      (normUnits K L).range = H := by
  obtain ⟨L, hL, hG, hc, hLH⟩ := exists_range_normUnits_eq (Ω := Ω) H hH
  exact ⟨L, hL, { toIsGalois := hG, toIsMulCommutative := ⟨⟨hc⟩⟩ }, hLH⟩

end Lattice

section OrderIso

variable (K) in

def openFiniteIndexSubgroups : Set (Subgroup Kˣ) :=
  {H | IsOpen (H : Set Kˣ) ∧ H.FiniteIndex}

variable (K Ω) in

def normGroupMap (L : finiteAbelianExtensions K Ω) : openFiniteIndexSubgroups K :=
  have := L.2.1
  ⟨(normUnits K (L : IntermediateField K Ω)).range,
    isOpen_range_normUnits_and_finiteIndex (Ω := Ω) _⟩

theorem normGroupMap_injective : Function.Injective (normGroupMap K Ω) := by
  intro L L' h
  have := L.2.1
  have := L.2.2
  have := L'.2.1
  have := L'.2.2
  have h' : (normUnits K (L : IntermediateField K Ω)).range =
      (normUnits K (L' : IntermediateField K Ω)).range := congrArg Subtype.val h
  exact Subtype.ext (le_antisymm (range_normUnits_le_iff.1 h'.ge) (range_normUnits_le_iff.1 h'.le))

theorem normGroupMap_surjective : Function.Surjective (normGroupMap K Ω) := by
  intro H
  have := H.2.2
  obtain ⟨L, h1, h2, hL⟩ := exists_isAbelianGalois_range_normUnits_eq (Ω := Ω) H.1 H.2.1
  exact ⟨⟨L, h1, h2⟩, Subtype.ext hL⟩

theorem normGroupMap_le_iff {L L' : finiteAbelianExtensions K Ω} :
    normGroupMap K Ω L ≤ normGroupMap K Ω L' ↔ L' ≤ L := by
  have := L.2.1
  have := L.2.2
  have := L'.2.1
  have := L'.2.2
  exact range_normUnits_le_iff

variable (K Ω) in

def normGroupOrderIso : finiteAbelianExtensions K Ω ≃o (openFiniteIndexSubgroups K)ᵒᵈ where
  toEquiv := (Equiv.ofBijective _ ⟨normGroupMap_injective, normGroupMap_surjective⟩).trans
    OrderDual.toDual
  map_rel_iff' := normGroupMap_le_iff

theorem normGroupOrderIso_apply (L : finiteAbelianExtensions K Ω) :
    (OrderDual.ofDual (normGroupOrderIso K Ω L)).1 =
      (have := L.2.1; (normUnits K (L : IntermediateField K Ω)).range) :=
  rfl

end OrderIso

end GroundTheory.LocalField
