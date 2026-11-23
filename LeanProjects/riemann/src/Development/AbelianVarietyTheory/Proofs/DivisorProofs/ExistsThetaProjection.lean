import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem theta_map_smul_fontaine {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]
    (σ : Λ →+* O) (f : RL p O Λ →+* O) (hf : IsTheta σ f) (a : Ainf p O) (r : RL p O Λ) :
    f (a • r) = WittVector.fontaineTheta O p a * f r := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  have := hf a 1
  simpa [Algebra.TensorProduct.algebraMap_apply] using this

theorem proj_exists (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (C : Type) [Field C] [Algebra O C] (Λ : Type)
    [CommRing Λ] [Algebra ℤ_[p] Λ] (N h : ℕ) (σ : Λ →+* O) (f : RL p O Λ →+* O)
    (e : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) :
    IsTheta σ f → ∃ π, IsProj C e f π := by
  intro hf
  let M : Matrix (Fin N) (Fin h) C := fun i j => algebraMap O C (f (e.symm (Pi.single j 1) i))
  refine ⟨Matrix.mulVecLin M, ?_⟩
  intro w
  have hw : w = ∑ j, e w j • e.symm (Pi.single j 1) := by
    apply e.injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  funext i
  conv_rhs => rw [hw]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, M, Finset.sum_apply, Pi.smul_apply,
    map_sum, theta_map_smul_fontaine σ f hf, map_mul]
  show (M *ᵥ _) i = _
  simp only [Matrix.mulVec, dotProduct, M]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end GlobalTheory.DetInv
