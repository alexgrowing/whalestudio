import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBoxRadiiAtEntry
open ValuativeRel Matrix GlobalTheory.SplitFlip GlobalTheory.FullRankCoinv GlobalTheory.RankCoinv GlobalTheory.NormalCore

namespace GlobalTheory.CharSplit

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_eq_zpow_unif {ϖ : kˣ} (hϖ : IsUnif ϖ) (d : kˣ) :
    ∃ e : ℤ, valuation k (d : k) = valuation k (ϖ : k) ^ e := by
  let φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  have h1 : φ (uniformizer k) = WithZero.exp (-1) := by
    apply le_antisymm
    · have : φ (uniformizer k) < 1 := by
        rw [← map_one φ]
        exact φ.strictMono uniformizer_lt_one
      have h0 : φ (uniformizer k) ≠ 0 := by simpa using uniformizer_ne_zero
      rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
      rw [← WithZero.exp_log h0, WithZero.exp_le_exp]
      omega
    · have : φ.symm (WithZero.exp (-1)) < 1 := by
        rw [← map_one φ.symm]
        refine φ.symm.strictMono ?_
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        omega
      simpa using φ.strictMono.monotone (le_uniformizer_iff.2 this)
  have h0 : φ (valuation k (d : k)) ≠ 0 := by simp
  refine ⟨-WithZero.log (φ (valuation k (d : k))), φ.injective ?_⟩
  change φ _ = φ _
  rw [hϖ, map_zpow₀, h1, ← WithZero.exp_zsmul]
  simp [WithZero.exp_log h0]

theorem exists_zpow_mul_unit {ϖ : kˣ} (hϖ : IsUnif ϖ) (x : kˣ) :
    ∃ (m : ℤ) (u : kˣ), valuation k (u : k) = 1 ∧ x = ϖ ^ m * u := by
  obtain ⟨e, he⟩ := valuation_eq_zpow_unif hϖ x
  refine ⟨e, ϖ ^ (-e) * x, ?_, by group⟩
  have h0 : valuation k (ϖ : k) ^ e ≠ 0 := zpow_ne_zero _ ((Valuation.ne_zero_iff _).2 ϖ.ne_zero)
  rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, he, _root_.zpow_neg]
  exact inv_mul_cancel₀ h0

theorem ne_one_unif_or_unit : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ), IsUnif ϖ → ν ≠ 1 →
    ν ϖ ≠ 1 ∨ ∃ u : kˣ, valuation k (u : k) = 1 ∧ ν u ≠ 1 := by
  intro k _ _ _ _ ν ϖ hϖ hν
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  apply hν
  ext1 x
  obtain ⟨m, u, hu, rfl⟩ := exists_zpow_mul_unit hϖ x
  rw [map_mul, map_zpow, h1, h2 u hu, _root_.one_zpow, one_mul, MonoidHom.one_apply]

end GlobalTheory.CharSplit
