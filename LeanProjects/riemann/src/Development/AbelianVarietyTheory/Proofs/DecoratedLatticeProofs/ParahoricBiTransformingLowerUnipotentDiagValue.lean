import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportParahoricBiTransformingLeviDoubleCoset
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricDoubleCosetValuation
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke
open Classical

namespace GlobalTheory.LowerHeckeSupp

theorem lowU_add {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (a b : Matrix D A k) :
    lowU (a + b) = lowU a * lowU b := by
  ext1
  rw [Units.val_mul, val_lowU, val_lowU, val_lowU, fromBlocks_multiply]
  simp [add_comm]

theorem biType_lowU_emb : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ξ : kˣ →* ℂˣ), IsTame ξ → ¬ IsUnram ξ → ∀ φ : GL (A ⊕ D) k → ℂ, IsBiType ξ φ → ∀ (ν : Matrix D A k) (y : GL D k), φ (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, y)) = if ∃ ν₁ ν₂ : Matrix D A k, (∀ i a, valuation k (ν₁ i a) < 1) ∧ (∀ i a, valuation k (ν₂ i a) < 1) ∧ ν = ν₁ + y.1 * ν₂ then φ (emb₂ k (Equiv.refl (A ⊕ D)) (1, y)) else 0 := by
  intro k _ _ _ _ A D _ _ _ _ ξ hT hU φ hφ ν y
  split_ifs with h
  · obtain ⟨ν₁, ν₂, h₁, h₂, rfl⟩ := h
    have hd : ∀ μ : Matrix D A k, ((1 : kˣ) : k) = ((lowU μ : GL (A ⊕ D) k) : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det := by
      intro μ; simp [val_lowU]
    rw [lowU_add, mul_assoc, ← emb_mul_lowU]
    rw [(hφ _ (lowU_mem h₁) 1 (hd ν₁) _).1, (hφ _ (lowU_mem h₂) 1 (hd ν₂) _).2]
    simp
  · by_contra hne
    obtain ⟨x, z, j, hj, j', hj', he⟩ := GlobalTheory.ParHeckeSupp.support_levi k A D ξ hT hU φ hφ _ hne
    have hv : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, y)).1 = fromBlocks 1 0 ν y.1 := by
      rw [Units.val_mul, val_lowU, val_emb_one, fromBlocks_multiply]; simp
    exact h (GlobalTheory.ParHeckeCap.lowerUni_mem_cap k A D _ ν y hv ⟨x, z, j, hj, j', hj', he⟩)

end GlobalTheory.LowerHeckeSupp
