import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_unit_valuation_eq_of_adm :
    ∀ (F : Type) [Field F] [NumberField F] (S T : Finset (HeightOneSpectrum (𝓞 F)))
      (n : HeightOneSpectrum (𝓞 F) → ℤ), admitted F S → (∀ v, v ∉ T → n v = 0) →
      ∃ a : Fˣ, ∀ v, v ∉ S → v.valuation F (a : F) = WithZero.exp (n v) := by
  intro F _ _ S T n hS hT
  classical
  have key : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∃ π : Fˣ,
      v.valuation F (π : F) = WithZero.exp (-1) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → w ≠ v → w.valuation F (π : F) = 1 := by
    intro v hv
    obtain ⟨-, π, h1, h2⟩ := hS v hv
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at h1
      exact WithZero.exp_ne_zero h1.symm
    exact ⟨Units.mk0 π hπ0, h1, h2⟩
  choose! π hπ1 hπ2 using key
  refine ⟨∏ w ∈ T.filter (· ∉ S), (π w) ^ (-n w), ?_⟩
  intro v hv
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, map_prod, map_zpow₀]
  by_cases hvT : v ∈ T
  · rw [Finset.prod_eq_single v]
    · rw [hπ1 v hv, ← WithZero.exp_zsmul]
      congr 1
      simp
    · intro w hw hwv
      rw [hπ2 w (Finset.mem_filter.1 hw).2 v hv (Ne.symm hwv), one_zpow]
    · intro h
      exact absurd (Finset.mem_filter.2 ⟨hvT, hv⟩) h
  · rw [hT v hvT, WithZero.exp_zero]
    refine Finset.prod_eq_one fun w hw => ?_
    have hne : v ≠ w := fun h => hvT (h ▸ (Finset.mem_filter.1 hw).1)
    rw [hπ2 w (Finset.mem_filter.1 hw).2 v hv hne, one_zpow]

end GlobalTheory.QNorm
