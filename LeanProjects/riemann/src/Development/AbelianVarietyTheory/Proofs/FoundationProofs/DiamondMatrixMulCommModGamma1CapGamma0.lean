import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory.KZ

theorem isDiam_mul_comm_mod_Gam (N l d d' : ℕ) (σ σ' : SL(2, ℤ)) (h : IsDiam N l d σ) (h' : IsDiam N l d' σ') :
    ∃ g : SL(2, ℤ), g ∈ Gam N l ∧ σ' * σ = g * (σ * σ') := by
  obtain ⟨⟨h0, h1⟩, -⟩ := h
  obtain ⟨⟨h0', h1'⟩, -⟩ := h'
  refine ⟨σ' * σ * (σ * σ')⁻¹, ⟨?_, ?_⟩, by group⟩
  · set a : CongruenceSubgroup.Gamma0 N := ⟨σ, h0⟩ with ha
    set b : CongruenceSubgroup.Gamma0 N := ⟨σ', h0'⟩ with hb
    have hu : (CongruenceSubgroup.Gamma0Map N).toHomUnits (b * a * (a * b)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul,
        mul_comm ((CongruenceSubgroup.Gamma0Map N).toHomUnits b), mul_inv_cancel]
    have h3 : b * a * (a * b)⁻¹ ∈ CongruenceSubgroup.Gamma1' N := by
      rw [CongruenceSubgroup.Gamma1_mem', ← MonoidHom.coe_toHomUnits, hu, Units.val_one]
    exact (CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h3)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1' h1) (Subgroup.inv_mem _ (Subgroup.mul_mem _ h1 h1'))

end GlobalTheory.KZ
