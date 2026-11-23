import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem uniformizer_zpow_mem_integers_iff :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (z : ℤ), (GLnLocal.uniformizer F : F) ^ z ∈ 𝒪[F] ↔ 0 ≤ z := by
  intro F _ _ _ _ z
  constructor
  · intro h
    by_contra hz
    have hz' : 0 < -z := by omega
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hz'.le
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp at hm
      omega
    have hlt := GLnLocal.valuation_uniformizer_lt_one F
    have hpow : (GLnLocal.uniformizer F : F) ^ m ∈ 𝒪[F] :=
      Subring.pow_mem _ (GLnLocal.uniformizer F).2 m
    have hne : (GLnLocal.uniformizer F : F) ≠ 0 := by
      intro h0
      have h1 := GLnLocal.uniformizer_ne_zero F
      exact h1 h0
    have hone : (GLnLocal.uniformizer F : F) ^ z * (GLnLocal.uniformizer F : F) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_add₀ hne, ← hm]
      simp
    have hv : ValuativeRel.valuation F ((GLnLocal.uniformizer F : F) ^ z) ≤ 1 := h
    have hvm : ValuativeRel.valuation F ((GLnLocal.uniformizer F : F) ^ m) < 1 := by
      rw [map_pow]
      exact pow_lt_one₀ zero_le' hlt hm0
    have h2 : ValuativeRel.valuation F
        ((GLnLocal.uniformizer F : F) ^ z * (GLnLocal.uniformizer F : F) ^ m) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hv) hvm
    rw [hone, map_one] at h2
    exact lt_irrefl _ h2
  · intro h
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [zpow_natCast]
    exact Subring.pow_mem _ (GLnLocal.uniformizer F).2 m

end GlobalTheory.CompanionTheory.LFUDom
