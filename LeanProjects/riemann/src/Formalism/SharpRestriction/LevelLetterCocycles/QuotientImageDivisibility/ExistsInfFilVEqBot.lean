import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound.MC

open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

section Fil

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filB_anti : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti

private theorem range_tensor_map_subtype_mono {S T : Submodule Qp BdR} (h : S ≤ T) :
    LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) S.subtype) ≤
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) T.subtype) := by
  rintro _ ⟨w, rfl⟩
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => exact LinearMap.mem_range.mpr ⟨x ⊗ₜ[Qp] ⟨(y : BdR), h y.2⟩, by simp⟩
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add]
    exact add_mem h₁ h₂

theorem filVB_anti : Antitone (FilV PD (LL := LL) (V := V)) := by
  intro a b hab
  exact range_tensor_map_subtype_mono (S := (PD.Fil b).restrictScalars Qp) (T := (PD.Fil a).restrictScalars Qp)
    fun y hy => filB_anti PD hab hy

private theorem mem_FilV_iff' (a : ℤ) (z : V ⊗[Qp] BdR) :
    z ∈ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a ↔
      ∃ w, AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        ((PD.Fil a).restrictScalars Qp).subtype w = z := Iff.rfl

theorem tmul_mem_filV (a : ℤ) (x : V) {y : BdR} (hy : y ∈ PD.Fil a) :
    x ⊗ₜ[Qp] y ∈ FilV PD (LL := LL) (V := V) a :=
  (mem_FilV_iff' PD a _).mpr
    ⟨x ⊗ₜ[Qp] (⟨y, hy⟩ : (PD.Fil a).restrictScalars Qp), by simp⟩

theorem filV_exh (z : V ⊗[Qp] BdR) : ∃ a : ℤ, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, ha⟩ := PD.Fil_exh y
    exact ⟨a, tmul_mem_filV PD a x ha⟩
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨a₁, ha₁⟩ := h₁
    obtain ⟨a₂, ha₂⟩ := h₂
    exact ⟨min a₁ a₂, add_mem (filVB_anti PD (min_le_left _ _) ha₁)
      (filVB_anti PD (min_le_right _ _) ha₂)⟩

theorem coord_mem {ι : Type} (b : Basis ι Qp V) (a : ℤ) (z : V ⊗[Qp] BdR)
    (hz : z ∈ FilV PD (LL := LL) (V := V) a) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft b z i ∈ PD.Fil a := by
  obtain ⟨w, rfl⟩ := (mem_FilV_iff' PD a z).mp hz
  clear hz
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.subtype_apply,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    exact Submodule.smul_of_tower_mem (PD.Fil a) _ y.2
  | add w₁ w₂ h₁ h₂ =>
    rw [map_add, map_add, Finsupp.add_apply]
    exact add_mem h₁ h₂

theorem filV_sep (z : V ⊗[Qp] BdR) (hz : ∀ a : ℤ, z ∈ FilV PD (LL := LL) (V := V) a) : z = 0 := by
  apply (TensorProduct.equivFinsuppOfBasisLeft (Basis.ofVectorSpace Qp V)).injective
  rw [map_zero]
  ext i
  rw [Finsupp.zero_apply]
  refine PD.Fil_sep _ fun a => ?_
  convert coord_mem PD (Basis.ofVectorSpace Qp V) a z (hz a) i

private theorem exists_int_finset_subset_FilV (s : Finset (V ⊗[Qp] BdR)) :
    ∃ a : ℤ, ∀ z ∈ s, z ∈ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨a, ha⟩ := ih
    obtain ⟨c, hc⟩ := filV_exh PD (LL := LL) x
    refine ⟨min a c, fun z hz => ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact filVB_anti PD (min_le_right _ _) hc
    · exact filVB_anti PD (min_le_left _ _) (ha z hz)

theorem exists_le_filV (D : Submodule LL (V ⊗[Qp] BdR)) [FiniteDimensional LL D] :
    ∃ a : ℤ, D ≤ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨s, hs⟩ := (Module.Finite.iff_fg (N := D)).mp inferInstance
  obtain ⟨a, ha⟩ := exists_int_finset_subset_FilV PD (LL := LL) (V := V) s
  refine ⟨a, ?_⟩
  rw [← hs]
  exact Submodule.span_le.mpr fun z hz => ha z (Finset.mem_coe.mp hz)

theorem exists_inf_filV_eq_bot (D : Submodule LL (V ⊗[Qp] BdR)) [FiniteDimensional LL D] :
    ∃ a : ℤ, D ⊓ FilV PD (LL := LL) (V := V) a = ⊥ := by
  let S : ℤ → Submodule LL D := fun a => (Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a).comap D.subtype
  have hex : ∃ n : ℕ, ∃ a : ℤ, finrank LL (S a) = n := ⟨_, 0, rfl⟩
  obtain ⟨a₀, ha₀⟩ := Nat.find_spec hex
  refine ⟨a₀, eq_bot_iff.mpr ?_⟩
  rintro x ⟨hxD, hxF⟩
  rw [Submodule.mem_bot]
  refine filV_sep PD (LL := LL) x fun b => ?_
  rcases le_total b a₀ with hb | hb
  · exact filVB_anti PD hb hxF
  · have hle : S b ≤ S a₀ := Submodule.comap_mono (filVB_anti PD hb)
    have heq : S b = S a₀ :=
      Submodule.eq_of_le_of_finrank_eq hle
        (le_antisymm (Submodule.finrank_mono hle) (ha₀ ▸ Nat.find_min' hex ⟨b, rfl⟩))
    have hx : (⟨x, hxD⟩ : D) ∈ S a₀ := hxF
    rw [← heq] at hx
    exact hx

end Fil

end Formalism.MainNotions.N.Pv.LocalLengthBound.MC
