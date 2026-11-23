import Mathlib

namespace GlobalTheory.SmulMemSpanIntegers

theorem exists_smul_mem_span_integers {Ks : Type} [Field Ks] [NumberField Ks] {WL : Type}
    [AddCommGroup WL] [Module Ks WL] [Module (NumberField.RingOfIntegers Ks) WL]
    [IsScalarTower (NumberField.RingOfIntegers Ks) Ks WL] {T : Set WL} {g : WL}
    (hg : g ∈ Submodule.span Ks T) :
    ∃ d : NumberField.RingOfIntegers Ks, d ≠ 0 ∧
      d • g ∈ Submodule.span (NumberField.RingOfIntegers Ks) T := by

  induction hg using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.subset_span hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨d₁, hd₁, h₁⟩ := ihx
    obtain ⟨d₂, hd₂, h₂⟩ := ihy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (x + y) = d₂ • (d₁ • x) + d₁ • (d₂ • y) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm d₁ d₂ x]
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ h₁) (Submodule.smul_mem _ _ h₂)
  | smul c x _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers Ks) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : algebraMap (NumberField.RingOfIntegers Ks) Ks b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ Ks)).2 hb0
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have e : b • ((algebraMap (NumberField.RingOfIntegers Ks) Ks a /
        algebraMap (NumberField.RingOfIntegers Ks) Ks b) • x) = a • x := by
      rw [← smul_assoc, Algebra.smul_def, mul_div_cancel₀ _ hbK, algebraMap_smul]
    rw [mul_comm, mul_smul, e, smul_comm]
    exact Submodule.smul_mem _ _ h

end GlobalTheory.SmulMemSpanIntegers
