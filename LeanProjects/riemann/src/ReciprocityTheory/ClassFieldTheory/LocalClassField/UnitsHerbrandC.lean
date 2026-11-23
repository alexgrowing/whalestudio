import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandB

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable (K L : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

noncomputable def Phi : L ≃L[K] ((L ≃ₐ[K] L) → K) :=
  (IsGalois.normalBasis K L).equivFun.toContinuousLinearEquiv

variable {K L}

theorem Phi_symm_apply (c : (L ≃ₐ[K] L) → K) :
    (Phi K L).symm c = ∑ σ, c σ • σ (IsGalois.normalBasis K L 1) := by
  show (IsGalois.normalBasis K L).equivFun.symm c = _
  rw [Module.Basis.equivFun_symm_apply]
  exact Finset.sum_congr rfl fun σ _ => by rw [IsGalois.normalBasis_apply]

theorem Phi_map (σ : L ≃ₐ[K] L) (x : L) (τ : L ≃ₐ[K] L) : Phi K L (σ x) τ = Phi K L x (σ⁻¹ * τ) := by
  have : σ x = (Phi K L).symm (fun τ => Phi K L x (σ⁻¹ * τ)) := by
    rw [Phi_symm_apply]
    calc σ x = σ ((Phi K L).symm (Phi K L x)) := by simp
      _ = ∑ ρ, Phi K L x ρ • (σ * ρ) (IsGalois.normalBasis K L 1) := by
        rw [Phi_symm_apply, map_sum]
        exact Finset.sum_congr rfl fun ρ _ => by rw [map_smul]; rfl
      _ = ∑ τ, Phi K L x (σ⁻¹ * τ) • τ (IsGalois.normalBasis K L 1) :=
        Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun ρ => by simp)
  rw [this, ContinuousLinearEquiv.apply_symm_apply]

theorem norm_Phi_map (σ : L ≃ₐ[K] L) (x : L) : ‖Phi K L (σ x)‖ ≤ ‖Phi K L x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro τ
  rw [Phi_map]
  exact norm_le_pi_norm _ _

variable (K L) in

noncomputable def proj1 : L →+ L where
  toFun x := Phi K L x 1 • IsGalois.normalBasis K L 1
  map_zero' := by simp
  map_add' x y := by rw [map_add, Pi.add_apply, add_smul]

theorem norm_Phi_proj1 (x : L) : ‖Phi K L (proj1 K L x)‖ ≤ ‖Phi K L x‖ := by
  classical
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro τ
  show ‖Phi K L (Phi K L x 1 • IsGalois.normalBasis K L 1) τ‖ ≤ _
  rw [map_smul, Pi.smul_apply]
  have : Phi K L (IsGalois.normalBasis K L 1) τ = if 1 = τ then 1 else 0 :=
    Module.Basis.equivFun_self _ _ _
  rw [this, smul_eq_mul]
  split_ifs
  · rw [mul_one]; exact norm_le_pi_norm _ _
  · rw [mul_zero, norm_zero]; exact norm_nonneg _

theorem sum_proj1 (x : L) : ∑ σ : L ≃ₐ[K] L, σ • proj1 K L (σ⁻¹ • x) = x := by
  calc ∑ σ : L ≃ₐ[K] L, σ • proj1 K L (σ⁻¹ • x)
      = ∑ σ : L ≃ₐ[K] L, Phi K L x σ • σ (IsGalois.normalBasis K L 1) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        show σ (Phi K L (σ⁻¹ x) 1 • IsGalois.normalBasis K L 1) = _
        rw [map_smul, Phi_map, inv_inv, mul_one]
    _ = x := by rw [← Phi_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem norm_le_Phi (x : L) : ‖x‖ ≤ ‖((Phi K L).symm : ((L ≃ₐ[K] L) → K) →L[K] L)‖ * ‖Phi K L x‖ := by
  have := ((Phi K L).symm : ((L ≃ₐ[K] L) → K) →L[K] L).le_opNorm (Phi K L x)
  simpa using this

theorem norm_Phi_le (x : L) : ‖Phi K L x‖ ≤ ‖(Phi K L : L →L[K] ((L ≃ₐ[K] L) → K))‖ * ‖x‖ :=
  (Phi K L : L →L[K] ((L ≃ₐ[K] L) → K)).le_opNorm x

theorem exists_consts : ∃ A B C : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ (∀ x : L, ‖x‖ ≤ A * ‖Phi K L x‖) ∧
    (∀ x : L, ‖Phi K L x‖ ≤ B * ‖x‖) ∧ ∀ x y : L, ‖Phi K L (x * y)‖ ≤ C * ‖Phi K L x‖ * ‖Phi K L y‖ := by
  set A := ‖((Phi K L).symm : ((L ≃ₐ[K] L) → K) →L[K] L)‖
  set B := ‖(Phi K L : L →L[K] ((L ≃ₐ[K] L) → K))‖
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  refine ⟨A, B, B * A * A, hA, hB, by positivity, norm_le_Phi, norm_Phi_le, fun x y => ?_⟩
  calc ‖Phi K L (x * y)‖ ≤ B * ‖x * y‖ := norm_Phi_le _
    _ = B * (‖x‖ * ‖y‖) := by rw [norm_mul]
    _ ≤ B * ((A * ‖Phi K L x‖) * (A * ‖Phi K L y‖)) := by
      gcongr
      · exact norm_le_Phi x
      · exact norm_le_Phi y
    _ = B * A * A * ‖Phi K L x‖ * ‖Phi K L y‖ := by ring

variable (K L) in

def ball (t : ℝ) (ht : 0 ≤ t) : AddSubgroup L where
  carrier := {x | ‖Phi K L x‖ ≤ t}
  zero_mem' := by simpa using ht
  add_mem' := fun {x y} hx hy => by
    show ‖Phi K L (x + y)‖ ≤ t
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  neg_mem' := fun {x} hx => by
    show ‖Phi K L (-x)‖ ≤ t
    rw [map_neg, norm_neg]; exact hx

theorem mem_ball {t : ℝ} {ht : 0 ≤ t} {x : L} : x ∈ ball K L t ht ↔ ‖Phi K L x‖ ≤ t := Iff.rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
