import Mathlib

namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open scoped Pointwise

theorem count {G X : Type*} [Group G] [MulAction G X] (J A : Subgroup G) (hAJ : A ≤ J)
    (hn : ∀ j ∈ J, ∀ a ∈ A, j * a * j⁻¹ ∈ A) (y : X) :
    Nat.card ((fun j : G => j • ((fun a : G => a • y) '' (A : Set G))) '' (J : Set G)) *
      (A ⊓ MulAction.stabilizer G y).relIndex (J ⊓ MulAction.stabilizer G y) = A.relIndex J := by
  classical
  set P : Set X := (fun a : G => a • y) '' (A : Set G) with hP
  set S := MulAction.stabilizer G y with hS
  have hsmul : ∀ u : J, u • P = (u : G) • P := fun u => rfl
  have himg : ((fun j : G => j • P) '' (J : Set G)) = MulAction.orbit J P := by
    ext Q
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, j.2, rfl⟩
  have hAP : ∀ u ∈ A, u • P = P := by
    intro u hu
    ext x
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨u * a, A.mul_mem hu ha, mul_smul u a y⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨(u⁻¹ * a) • y, ⟨u⁻¹ * a, A.mul_mem (A.inv_mem hu) ha, rfl⟩, ?_⟩
      simp [mul_smul]
  have hSP : ∀ s ∈ J, s ∈ S → s • P = P := by
    intro s hsJ hsS
    have hsy : s • y = y := hsS
    ext x
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      refine ⟨s * a * s⁻¹, hn s hsJ a ha, ?_⟩
      show (s * a * s⁻¹) • y = s • a • y
      conv_lhs => rw [← hsy]
      simp [mul_smul]
    · rintro ⟨a, ha, rfl⟩
      have h1 : s⁻¹ * a * s⁻¹⁻¹ ∈ A := hn s⁻¹ (J.inv_mem hsJ) a ha
      rw [inv_inv] at h1
      refine ⟨(s⁻¹ * a * s) • y, ⟨_, h1, rfl⟩, ?_⟩
      show s • (s⁻¹ * a * s) • y = a • y
      rw [mul_smul, mul_smul, hsy, smul_inv_smul]
  have hstab : MulAction.stabilizer J P = A.subgroupOf J ⊔ S.subgroupOf J := by
    apply le_antisymm
    · intro u hu
      have hu' : (u : G) • P = P := hu
      have hy : (u : G) • y ∈ P := by
        rw [← hu']
        exact Set.smul_mem_smul_set ⟨1, A.one_mem, one_smul G y⟩
      obtain ⟨a, ha, hay⟩ := hy
      have hay' : a • y = (u : G) • y := hay
      have haJ : a ∈ J := hAJ ha
      have hs : a⁻¹ * (u : G) ∈ S := by
        show (a⁻¹ * (u : G)) • y = y
        rw [mul_smul, ← hay', inv_smul_smul]
      have e : u = (⟨a, haJ⟩ : J) * ⟨a⁻¹ * u, J.mul_mem (J.inv_mem haJ) u.2⟩ := by
        ext
        simp
      rw [e]
      exact Subgroup.mul_mem_sup (show (⟨a, haJ⟩ : J) ∈ A.subgroupOf J from ha)
        (show (⟨a⁻¹ * u, J.mul_mem (J.inv_mem haJ) u.2⟩ : J) ∈ S.subgroupOf J from hs)
    · refine sup_le ?_ ?_
      · intro u hu
        show u • P = P
        rw [hsmul]
        exact hAP u hu
      · intro u hu
        show u • P = P
        rw [hsmul]
        exact hSP u u.2 hu
  have hnorm : (A.subgroupOf J).Normal := ⟨fun a ha g => by
    show ((g * a * g⁻¹ : J) : G) ∈ A
    simpa using hn g g.2 a ha⟩
  have hcard : Nat.card ((fun j : G => j • P) '' (J : Set G)) = (A.subgroupOf J ⊔ S.subgroupOf J).index := by
    rw [himg, ← hstab, MulAction.index_stabilizer]
    rfl
  have hb : (A ⊓ S).relIndex (J ⊓ S) = (A.subgroupOf J).relIndex (S.subgroupOf J) := by
    rw [← Subgroup.inf_subgroupOf_right S J, Subgroup.relIndex_subgroupOf inf_le_right]
    have h1 := Subgroup.relIndex_inf_mul_relIndex A S (J ⊓ S)
    rw [(Subgroup.relIndex_eq_one).2 inf_le_right, mul_one] at h1
    rw [← h1, show S ⊓ (J ⊓ S) = J ⊓ S from inf_of_le_right inf_le_right, inf_comm J S]
  have hm := Subgroup.relIndex_mul_index (le_sup_left : A.subgroupOf J ≤ A.subgroupOf J ⊔ S.subgroupOf J)
  rw [Subgroup.relIndex_sup_left] at hm
  rw [hcard, hb, mul_comm, hm]
  rfl

end PositivityTheory.RgUd.T.Nil.Orb.BStep
