import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
import GroundTheory.LocalFields.ConductorReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupAbelianNatStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_real : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e : ℕ) (v : ℝ), 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M v, σ ^ p ∈ upperRamificationGroup F ↥M (min (2 * v) (v + e)) := by
  intro F _ _ _ _ M _ _ p e v hv hOrd σ hσ

  have hc : (0 : ℤ) ≤ ⌈v⌉ := Int.ceil_nonneg hv
  have hn : ((⌈v⌉.toNat : ℕ) : ℝ) = ((⌈v⌉ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hc
  have hσn : σ ∈ upperRamificationGroup F ↥M ((⌈v⌉.toNat : ℕ) : ℝ) := by
    rw [hn, ← upperRamificationGroup_eq_ceil]
    exact hσ
  have hpow := GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_nat' F M p e ⌈v⌉.toNat hOrd σ hσn

  have hvn : v ≤ ((⌈v⌉.toNat : ℕ) : ℝ) := by
    rw [hn]; exact Int.le_ceil v
  have hle : min (2 * v) (v + e) ≤ ((min (2 * ⌈v⌉.toNat) (⌈v⌉.toNat + e) : ℕ) : ℝ) := by
    push_cast
    exact min_le_min (by linarith) (by linarith)
  exact upperRamificationGroup_antitone F ↥M hle hpow

end GlobalTheory.PMon.Ram
