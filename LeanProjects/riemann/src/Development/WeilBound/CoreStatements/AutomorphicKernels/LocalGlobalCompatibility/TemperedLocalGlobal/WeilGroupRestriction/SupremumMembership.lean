import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace PositivityTheory.Pf1.CLGD.K

namespace SupremumMembership

theorem exists_mem_of_sup {Γ : Type*} [Group Γ] (H N : Subgroup Γ) [N.Normal] (hHN : H ⊔ N = ⊤)
    (H₁ H₂ : Subgroup Γ) (h1 : H ≤ H₁) (h12 : H₁ < H₂) : ∃ n ∈ H₂, n ∉ H₁ ∧ n ∈ N := by
  obtain ⟨g, hg2, hg1⟩ := SetLike.exists_of_lt h12
  have hg : g ∈ ((H ⊔ N : Subgroup Γ) : Set Γ) := by rw [hHN]; exact Subgroup.mem_top g
  rw [Subgroup.mul_normal H N] at hg
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hg
  have hx1 : x ∈ H₁ := h1 hx
  refine ⟨y, ?_, ?_, hy⟩
  · have : y = x⁻¹ * (x * y) := by group
    rw [this]
    exact H₂.mul_mem (H₂.inv_mem (h12.le hx1)) hg2
  · intro hy1
    exact hg1 (H₁.mul_mem hx1 hy1)

end SupremumMembership

open SupremumMembership in
theorem place_membership_of_sup : KillingPolyConst := by
  intro E Ω _ _ _ _ _ l a _ ha r hr
  have hcont : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).trace :=
    (Units.continuous_val.comp hr).matrix_trace
  set U : Set (G E Ω) := {g | (r g : Matrix (Fin a) (Fin a) (Qbar l)).trace ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne.preimage hcont
  have h1U : (1 : G E Ω) ∈ U := by
    show (r 1 : Matrix (Fin a) (Fin a) (Qbar l)).trace ≠ 0
    rw [map_one, Units.val_one, Matrix.trace_one, Fintype.card_fin]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp ha)
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1U
  have : N.toSubgroup.Normal := N.isNormal'
  refine ⟨N.toSubgroup, N.isNormal', N.isOpen', fun H hHN H₁ H₂ h1 h12 => ?_⟩
  obtain ⟨n, hn2, hn1, hnN⟩ := exists_mem_of_sup H N.toSubgroup hHN H₁ H₂ h1 h12
  exact ⟨n, hn2, hn1, hN hnN⟩

end PositivityTheory.Pf1.CLGD.K

end
