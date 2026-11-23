import Mathlib

theorem UpperTheory.Reformulated.B.ElementDenominator.eltDen.{u_1, u_2, u_3} :
    ∀ {K : Type u_1} [inst : Field K] {R : Type u_2} [inst_1 : CommRing R] [IsDomain R] [inst_3 : Algebra R K]
    [IsFractionRing R K] {V : Type u_3} [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V]
    [inst_7 : _root_.Module R V] [IsScalarTower R K V] (Y : Submodule R V) {y : V},
    y ∈ Submodule.span K (↑Y : Set V) → ∃ (s : R), s ≠ (0 : R) ∧ s • y ∈ Y := by
  intro K _ R _ _ _ _ V _ _ _ _ Y y hy
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Y.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, htz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    rw [smul_add]
    refine Y.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact Y.smul_mem t hsx
    · rw [mul_smul]
      exact Y.smul_mem s htz
  | smul c x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) c
    refine ⟨s * (b : R), mul_ne_zero hs (nonZeroDivisors.coe_ne_zero b), ?_⟩
    have h1 : (b : R) • (c • x) = a • x := by
      rw [← algebraMap_smul K (b : R) (c • x), smul_smul, mul_comm, hab, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact Y.smul_mem a hsx
