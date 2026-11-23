import Mathlib

noncomputable def UpperTheory.Reformulated.B.CayleySignature.IsLatIn :
    {R W : Type} →
      [inst : CommRing R] → [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submodule R W → Submodule R W → Prop :=
    fun {R W : Type} [CommRing R] [AddCommGroup W] [_root_.Module R W] (M V : Submodule R W) ↦
      M.FG ∧ M ≤ V ∧ ∀ x ∈ V, ∃ (c : R), c ≠ (0 : R) ∧ c • x ∈ M

theorem UpperTheory.Reformulated.B.CayleySignature.isLatIn_spanK :
    ∀ {O K V : Type} [inst : CommRing O] [IsDomain O] [inst_2 : Field K] [inst_3 : Algebra O K] [IsFractionRing O K]
      [inst_5 : AddCommGroup V] [inst_6 : _root_.Module K V] [inst_7 : _root_.Module O V] [inst_8 : IsScalarTower O K V]
      {N : Submodule O V}, N.FG → UpperTheory.Reformulated.B.CayleySignature.IsLatIn N (Submodule.restrictScalars O (Submodule.span K (↑N : Set V))) := by
  intro O K V _ _ _ _ _ _ _ _ _ N hN
  refine ⟨hN, fun x hx => Submodule.subset_span hx, fun x hx => ?_⟩
  rw [Submodule.restrictScalars_mem] at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact N.smul_mem b hay
    · rw [mul_smul]
      exact N.smul_mem a hbz
  | smul k y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors O) k
    refine ⟨a * (q : O), mul_ne_zero ha (nonZeroDivisors.coe_ne_zero q), ?_⟩
    have h1 : (q : O) • (k • y) = p • y := by
      rw [← algebraMap_smul K (q : O), smul_smul, mul_comm, hpq, algebraMap_smul]
    rw [mul_smul, h1, smul_comm]
    exact N.smul_mem p hay
