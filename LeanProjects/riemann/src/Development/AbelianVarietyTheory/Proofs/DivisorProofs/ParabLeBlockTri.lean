import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity

noncomputable section

namespace GlobalTheory.HcIrr

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ}

def natBlocks (b : Fin r → Fin s) : Fin r → ℕ := fun i => (b i : ℕ)

theorem blockTri_le_parab (b : Fin r → Fin s) : blockTri (κ := K) (natBlocks b) ≤ parab K b := by
  intro p hp
  refine ⟨fun i j hij => hp hij, fun i j hij => ?_⟩
  exact (inv_mem hp : p⁻¹ ∈ blockTri (κ := K) (natBlocks b)) hij

theorem parab_le_blockTri (b : Fin r → Fin s) : parab K b ≤ blockTri (κ := K) (natBlocks b) := by
  intro p hp i j hij
  exact hp.1 i j hij

theorem levi_one (b : Fin r → Fin s) (c : Fin s) : levi K b c 1 = 1 := by
  apply Units.ext
  exact Matrix.submatrix_one _ Subtype.val_injective

theorem levi_mul (b : Fin r → Fin s) (c : Fin s) (p q : parab K b) :
    levi K b c (p * q) = levi K b c p * levi K b c q := by
  apply Units.ext
  exact blk_mul b c p.2.1 q.2.1

variable (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))

def leviTensor : Representation ℂ (blockTri (κ := K) (natBlocks b))
    (PiTensorProduct ℂ (fun c => (lam c : Type))) where
  toFun p := infl K b lam (Subgroup.inclusion (blockTri_le_parab b) p)
  map_one' := by
    have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) 1)) = LinearMap.id := by
      intro c
      rw [map_one, levi_one, map_one]
      rfl
    simp only [infl, this]
    exact PiTensorProduct.map_id
  map_mul' p q := by
    have : ∀ c, (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) (p * q))) =
        (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p)) ∘ₗ
          (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) q)) := by
      intro c
      rw [map_mul, levi_mul, map_mul]
      rfl
    simp only [infl, this]
    exact PiTensorProduct.map_comp _ _

theorem leviTensor_apply (p : blockTri (κ := K) (natBlocks b)) :
    leviTensor b lam p = PiTensorProduct.map (fun c =>
      (lam c).ρ (levi K b c (Subgroup.inclusion (blockTri_le_parab b) p))) := rfl

instance finiteTensor : FiniteDimensional ℂ (PiTensorProduct ℂ (fun c => (lam c : Type))) :=
  Module.Finite.of_basis (Basis.piTensorProduct fun c => Module.finBasis ℂ (lam c : Type))

end GlobalTheory.HcIrr
