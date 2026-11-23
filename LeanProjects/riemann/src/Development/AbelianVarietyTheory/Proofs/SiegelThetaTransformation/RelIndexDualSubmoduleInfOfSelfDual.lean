import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndNcardSetOfSubmoduleLeRelIndexEqLe

open Module

namespace GlobalTheory

section SelfDual

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem dualSubmodule_le_dualSubmodule_of_le (B : LinearMap.BilinForm ℚ V)
    {M N : Submodule ℤ V} (h : M ≤ N) : B.dualSubmodule N ≤ B.dualSubmodule M :=
  fun _ hx y hy => hx y (h hy)

theorem eq_zero_of_forall_rat_smul_mem (L : Submodule ℤ V) (hL : L.FG) {x : V}
    (hx : ∀ q : ℚ, q • x ∈ L) : x = 0 := by
  haveI : Module.Finite ℤ L := Module.Finite.iff_fg.2 hL
  haveI := Module.IsTorsionFree.trans_faithfulSMul ℤ ℚ V
  let b := Module.Free.chooseBasis ℤ L
  have h1 : x ∈ L := by simpa using hx 1
  have h2 : (⟨x, h1⟩ : L) = 0 := by
    refine b.repr.injective (Finsupp.ext fun i => ?_)
    rw [map_zero, Finsupp.zero_apply]
    set a := b.repr ⟨x, h1⟩ i with ha
    have hn : (0 : ℤ) < |a| + 1 := by positivity
    have h3 : (⟨x, h1⟩ : L) = (|a| + 1) • (⟨((|a| + 1 : ℤ) : ℚ)⁻¹ • x, hx _⟩ : L) := by
      apply Subtype.ext
      rw [Submodule.coe_smul, ← Int.cast_smul_eq_zsmul ℚ, smul_smul,
        mul_inv_cancel₀ (by exact_mod_cast hn.ne'), one_smul]
    refine Int.eq_zero_of_abs_lt_dvd (m := |a| + 1) ⟨b.repr ⟨_, hx ((|a| + 1 : ℤ) : ℚ)⁻¹⟩ i, ?_⟩
      (lt_add_one _)
    rw [← smul_eq_mul, ← Finsupp.smul_apply, ← map_smul, ← h3]
  exact congrArg Subtype.val h2

variable [FiniteDimensional ℚ V]

theorem isLattice_of_fg_dualSubmodule (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) (hL : L.FG) (hd : (B.dualSubmodule L).FG) : L.IsLattice ℚ := by
  refine ⟨hL, ?_⟩
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  have h0 : (B.toDual hB).symm φ = 0 := by
    refine eq_zero_of_forall_rat_smul_mem _ hd fun q y hy => ?_
    have h1 : B ((B.toDual hB).symm φ) y = 0 := by
      rw [LinearMap.BilinForm.apply_toDual_symm_apply]
      exact hle (Submodule.subset_span hy)
    rw [map_smul, LinearMap.smul_apply, h1, smul_zero]
    exact zero_mem _
  exact hφ (by simpa using h0)

theorem exists_basis_span_eq_of_isLattice (L : Submodule ℤ V) [L.IsLattice ℚ] :
    ∃ b : Basis (Fin (finrank ℚ V)) ℚ V, L = Submodule.span ℤ (Set.range b) := by
  have hr : finrank ℤ L = finrank ℚ V := by
    let b := Module.Free.chooseBasis ℤ L
    rw [finrank_eq_card_basis b, finrank_eq_card_basis (b.extendOfIsLattice ℚ)]
  let b := Module.finBasisOfFinrankEq ℤ L hr
  refine ⟨b.extendOfIsLattice ℚ, ?_⟩
  have h1 : Set.range (b.extendOfIsLattice ℚ) = L.subtype '' Set.range b := by
    rw [← Set.range_comp]
    congr 1
    exact funext fun i => b.extendOfIsLattice_apply ℚ i
  rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]

theorem finrank_eq_of_isLattice (L : Submodule ℤ V) [L.IsLattice ℚ] :
    finrank ℤ L = finrank ℚ V := by
  let b := Module.Free.chooseBasis ℤ L
  rw [finrank_eq_card_basis b, finrank_eq_card_basis (b.extendOfIsLattice ℚ)]

theorem isLattice_dualSubmodule (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    (L : Submodule ℤ V) [L.IsLattice ℚ] : (B.dualSubmodule L).IsLattice ℚ := by
  obtain ⟨b, rfl⟩ := exists_basis_span_eq_of_isLattice L
  rw [B.dualSubmodule_span_of_basis hB]
  exact ⟨Submodule.fg_span (Set.finite_range _), by
    rw [Submodule.span_span_of_tower, Basis.span_eq]⟩

omit [FiniteDimensional ℚ V] in

theorem relIndex_span_basis_eq_abs_det {ι : Type*} [DecidableEq ι] [Fintype ι]
    (b₁ b₂ : Basis ι ℚ V)
    (h : Submodule.span ℤ (Set.range b₁) ≤ Submodule.span ℤ (Set.range b₂)) :
    (((Submodule.span ℤ (Set.range b₁)).toAddSubgroup.relIndex
      (Submodule.span ℤ (Set.range b₂)).toAddSubgroup : ℕ) : ℚ) = |b₂.det b₁| :=
  AddSubgroup.relIndex_eq_abs_det _ _ h b₁ b₂ (Submodule.span_int_eq_addSubgroupClosure _)
    (Submodule.span_int_eq_addSubgroupClosure _)

theorem relIndex_ne_zero_of_isLattice {M N : Submodule ℤ V} [M.IsLattice ℚ] [N.IsLattice ℚ]
    (h : M ≤ N) : M.toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 := by
  obtain ⟨b₁, rfl⟩ := exists_basis_span_eq_of_isLattice M
  obtain ⟨b₂, rfl⟩ := exists_basis_span_eq_of_isLattice N
  intro h0
  have h1 := relIndex_span_basis_eq_abs_det b₁ b₂ h
  rw [h0, Nat.cast_zero, eq_comm, abs_eq_zero] at h1
  exact (b₂.isUnit_det b₁).ne_zero h1

theorem relIndex_dualSubmodule (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate)
    {M N : Submodule ℤ V} [M.IsLattice ℚ] [N.IsLattice ℚ] (h : M ≤ N) :
    (B.dualSubmodule N).toAddSubgroup.relIndex (B.dualSubmodule M).toAddSubgroup =
      M.toAddSubgroup.relIndex N.toAddSubgroup := by
  have h' := dualSubmodule_le_dualSubmodule_of_le B h
  obtain ⟨b₁, rfl⟩ := exists_basis_span_eq_of_isLattice M
  obtain ⟨b₂, rfl⟩ := exists_basis_span_eq_of_isLattice N
  rw [B.dualSubmodule_span_of_basis hB, B.dualSubmodule_span_of_basis hB] at h' ⊢
  apply Nat.cast_injective (R := ℚ)
  rw [relIndex_span_basis_eq_abs_det _ _ h, relIndex_span_basis_eq_abs_det _ _ h',
    Basis.det_apply, Basis.det_apply, ← Matrix.det_transpose (b₂.toMatrix b₁)]
  congr 2
  ext i j
  rw [Matrix.transpose_apply, Basis.toMatrix_apply, Basis.toMatrix_apply,
    LinearMap.BilinForm.dualBasis_repr_apply]
  conv_lhs => rw [← b₂.sum_repr (b₁ i)]
  simp only [map_sum, map_smul, LinearMap.BilinForm.apply_dualBasis_left]
  simp

theorem relIndex_dualSubmodule_inf_of_selfDual (B : LinearMap.BilinForm ℚ V)
    (hB : B.Nondegenerate) {L L' : Submodule ℤ V} [L.IsLattice ℚ] [L'.IsLattice ℚ]
    (hL : B.dualSubmodule L = L) (hL' : B.dualSubmodule L' = L') :
    L'.toAddSubgroup.relIndex (B.dualSubmodule (L ⊓ L')).toAddSubgroup =
      (L ⊓ L').toAddSubgroup.relIndex L.toAddSubgroup := by
  have h1 := relIndex_dualSubmodule B hB (inf_le_left : L ⊓ L' ≤ L)
  have h2 := relIndex_dualSubmodule B hB (inf_le_right : L ⊓ L' ≤ L')
  have l1 := dualSubmodule_le_dualSubmodule_of_le B (inf_le_left : L ⊓ L' ≤ L)
  have l2 := dualSubmodule_le_dualSubmodule_of_le B (inf_le_right : L ⊓ L' ≤ L')
  rw [hL] at h1 l1
  rw [hL'] at h2 l2
  have m1 := AddSubgroup.relIndex_mul_relIndex (L ⊓ L').toAddSubgroup L.toAddSubgroup
    (B.dualSubmodule (L ⊓ L')).toAddSubgroup (inf_le_left : L ⊓ L' ≤ L) l1
  have m2 := AddSubgroup.relIndex_mul_relIndex (L ⊓ L').toAddSubgroup L'.toAddSubgroup
    (B.dualSubmodule (L ⊓ L')).toAddSubgroup (inf_le_right : L ⊓ L' ≤ L') l2
  rw [h1] at m1
  rw [h2, ← m1] at m2
  rw [h2]
  exact Nat.mul_self_inj.1 m2

end SelfDual

theorem card_selfDual_le {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (B : LinearMap.BilinForm ℚ V) (hB : B.Nondegenerate) (hr : B.IsRefl)
    (hlr : ∀ x y, B x y = B y x ∨ B x y = - B y x) (L : Submodule ℤ V) (hL : L.FG) (hLd : B.dualSubmodule L = L) (m : ℕ) (hm : 1 ≤ m) :
    {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧ L'.toAddSubgroup.relIndex L.toAddSubgroup = m}.Finite ∧
    {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧ L'.toAddSubgroup.relIndex L.toAddSubgroup = m}.ncard ≤ m ^ (2 * Module.finrank ℚ V) ∧
    ∀ L' : Submodule ℤ V, L'.FG → B.dualSubmodule L' = L' → L'.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0 ∧ (L'.toAddSubgroup.relIndex L.toAddSubgroup = 1 → L' = L) := by
  have hm0 : m ≠ 0 := by omega
  haveI : L.IsLattice ℚ := isLattice_of_fg_dualSubmodule B hB L hL (hLd.symm ▸ hL)
  have hinf : ∀ L' : Submodule ℤ V, (L ⊓ L').toAddSubgroup.relIndex L.toAddSubgroup =
      L'.toAddSubgroup.relIndex L.toAddSubgroup := fun L' =>
    AddSubgroup.inf_relIndex_left L.toAddSubgroup L'.toAddSubgroup
  have hsub : {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧
      L'.toAddSubgroup.relIndex L.toAddSubgroup = m} ⊆
      ⋃ M ∈ {M : Submodule ℤ V | M.IsLattice ℚ ∧ M ≤ L ∧
        M.toAddSubgroup.relIndex L.toAddSubgroup = m},
        {H | H ≤ B.dualSubmodule M ∧
          H.toAddSubgroup.relIndex (B.dualSubmodule M).toAddSubgroup = m} := by
    rintro L' ⟨h1, h2, h3⟩
    haveI : L'.IsLattice ℚ := isLattice_of_fg_dualSubmodule B hB L' h1 (h2.symm ▸ h1)
    refine Set.mem_biUnion (x := L ⊓ L') ⟨inferInstance, inf_le_left, (hinf L').trans h3⟩ ⟨?_, ?_⟩
    · exact h2.ge.trans (dualSubmodule_le_dualSubmodule_of_le B inf_le_right)
    · rw [relIndex_dualSubmodule_inf_of_selfDual B hB hLd h2, hinf, h3]
  have hcard : {L' : Submodule ℤ V | L'.FG ∧ B.dualSubmodule L' = L' ∧
      L'.toAddSubgroup.relIndex L.toAddSubgroup = m}.encard ≤
      ((m ^ (2 * finrank ℚ V) : ℕ) : ℕ∞) := by
    rw [two_mul, pow_add]
    refine (Set.encard_le_encard hsub).trans (encard_biUnion_le_mul _ _ _ _ ?_ ?_)
    · rw [← finrank_eq_of_isLattice L]
      exact (Set.encard_le_encard fun M hM => hM.2).trans
        (encard_setOf_submodule_le_relIndex_eq_le L hm0)
    · intro M hM
      haveI := hM.1
      haveI := isLattice_dualSubmodule B hB M
      rw [← finrank_eq_of_isLattice (B.dualSubmodule M)]
      exact encard_setOf_submodule_le_relIndex_eq_le _ hm0
  have hf := Set.finite_of_encard_le_coe hcard
  refine ⟨hf, ?_, fun L' h1 h2 => ⟨?_, fun h3 => ?_⟩⟩
  · rw [← hf.cast_ncard_eq] at hcard
    exact_mod_cast hcard
  · haveI : L'.IsLattice ℚ := isLattice_of_fg_dualSubmodule B hB L' h1 (h2.symm ▸ h1)
    rw [← hinf]
    exact relIndex_ne_zero_of_isLattice inf_le_left
  · have h4 : L ≤ L' := AddSubgroup.relIndex_eq_one.1 h3
    refine le_antisymm ?_ h4
    have := dualSubmodule_le_dualSubmodule_of_le B h4
    rwa [hLd, h2] at this

end GlobalTheory
