import Mathlib
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section
open scoped BigOperators ComplexConjugate

namespace GlobalTheory.ThLoc.LocPull

open Formalism.L2.Th1.H (blk4 pow4 slice imgLat tens4 kernel4)

variable {n : Type} [Fintype n] [DecidableEq n]

def diagonalPowFourEquiv (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ) where
  toFun z w := φ (slice w.1 z) w.2
  invFun z w := φ.symm (slice w.1 z) w.2
  map_add' x y := by
    funext w
    have e : slice w.1 (x + y) = slice w.1 x + slice w.1 y := rfl
    simp only [e, map_add, Pi.add_apply]
  map_smul' c x := by
    funext w
    have e : slice w.1 (c • x) = c • slice w.1 x := rfl
    simp only [e, map_smul, Pi.smul_apply, RingHom.id_apply]
  left_inv z := by
    funext w
    have e : slice w.1 (fun w' : Fin 4 × n => φ (slice w'.1 z) w'.2) = φ (slice w.1 z) := rfl
    simp only [e, LinearEquiv.symm_apply_apply]
    rfl
  right_inv z := by
    funext w
    have e : slice w.1 (fun w' : Fin 4 × n => φ.symm (slice w'.1 z) w'.2) = φ.symm (slice w.1 z) := rfl
    simp only [e, LinearEquiv.apply_symm_apply]
    rfl

theorem slice_pow4E (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (a : Fin 4) (z : Fin 4 × n → ℂ) :
    slice a (diagonalPowFourEquiv φ z) = φ (slice a z) := rfl

theorem fourCopiesHermitianForm_eq_sum_blocks (h : Matrix n n ℂ) (x y : Fin 4 × n → ℂ) :
    matH (blk4 h) x y = ∑ a : Fin 4, matH h (slice a x) (slice a y) := by
  show (∑ w, ∑ w', x w * blk4 h w w' * conj (y w')) = ∑ a : Fin 4, ∑ i, ∑ j, x (a, i) * h i j * conj (y (a, j))
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp [blk4]
  · intro b _ hb
    simp [blk4, Ne.symm hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

theorem blockwiseActionOnFourCopies_isometry (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (h : Matrix n n ℂ)
    (hφ : IsIsom (matH h) (matH h) (φ : (n → ℂ) →ₗ[ℂ] (n → ℂ))) (x y : Fin 4 × n → ℂ) :
    matH (blk4 h) (diagonalPowFourEquiv φ x) (diagonalPowFourEquiv φ y) = matH (blk4 h) x y := by
  rw [fourCopiesHermitianForm_eq_sum_blocks, fourCopiesHermitianForm_eq_sum_blocks]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [slice_pow4E, slice_pow4E]
  exact hφ _ _

theorem imgLat_pull (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)) (Λ : AddSubgroup (n → ℂ))
    (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) :
    imgLat (((diagonalPowFourEquiv φ).trans g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ))
        (pow4 (Λ.comap φ.toLinearMap.toAddMonoidHom)) =
      imgLat (g : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 Λ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨diagonalPowFourEquiv φ x, fun a => hx a, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(diagonalPowFourEquiv φ).symm x, fun a => ?_, ?_⟩
    · show φ (slice a ((diagonalPowFourEquiv φ).symm x)) ∈ Λ
      rw [← slice_pow4E, LinearEquiv.apply_symm_apply]
      exact hx a
    · show g (diagonalPowFourEquiv φ ((diagonalPowFourEquiv φ).symm x)) = g x
      rw [LinearEquiv.apply_symm_apply]

theorem locNorm_pull : ∀ (a₀ : ℕ) (b₀ : ℤ) (dK : ℕ) (ha : 0 < a₀) (hdK : 0 < dK) (lam : ℂ) (hlam : lam ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (φ : (n → ℂ) ≃ₗ[ℂ] (n → ℂ)), IsIsom (matH h) (matH h) (φ : (n → ℂ) →ₗ[ℂ] (n → ℂ)) → LocNorm a₀ b₀ dK ha hdK lam hlam h Λ θ p ι → LocNorm a₀ b₀ dK ha hdK lam hlam h (Λ.comap φ.toLinearMap.toAddMonoidHom) (fun z => θ (φ z)) p ι := by
  intro a₀ b₀ dK ha hdK lam hlam n _ _ h Λ θ p _ ι φ hφ H
  obtain ⟨g₁, ε, hiso, hnd, hidx, hε, hker⟩ := H
  have hI := imgLat_pull φ Λ g₁
  refine ⟨(diagonalPowFourEquiv φ).trans g₁, ε, ?_, ?_, ?_, hε, ?_⟩
  · intro x y
    exact (hiso (diagonalPowFourEquiv φ x) (diagonalPowFourEquiv φ y)).trans (blockwiseActionOnFourCopies_isometry φ h hφ x y)
  · rw [hI]
    exact hnd
  · rw [hI]
    exact hidx
  · funext z
    have t1 : tens4 (fun z => θ (φ z)) z = tens4 θ (diagonalPowFourEquiv φ z) := rfl
    rw [t1, hker]
    simp only [Pi.smul_apply]
    congr 1
    unfold kernel4
    rw [hI]
    rfl

end GlobalTheory.ThLoc.LocPull
