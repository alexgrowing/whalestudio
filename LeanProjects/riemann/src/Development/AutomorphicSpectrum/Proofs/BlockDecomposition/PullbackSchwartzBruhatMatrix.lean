import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_block_concatenation (A B : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    Continuous fun M : Matrix (Fin 2) (Fin 2) F => cat3 (A * M * B) v := by
  have h : Continuous fun M : Matrix (Fin 2) (Fin 2) F => A * M * B :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  refine continuous_matrix fun i j => ?_
  have he : ∀ a b, Continuous fun M : Matrix (Fin 2) (Fin 2) F => (A * M * B) a b :=
    fun a b => h.matrix_elem a b
  fin_cases i <;> fin_cases j <;> simp [cat3] <;> first | exact he _ _ | exact continuous_const

def firstCols (X : Matrix (Fin 2) (Fin 3) F) : Matrix (Fin 2) (Fin 2) F :=
  Matrix.of fun i j => X i j.castSucc

theorem continuous_firstCols : Continuous (firstCols (F := F)) :=
  continuous_matrix fun i j => continuous_id.matrix_elem i j.castSucc

theorem first_columns_concatenation (A : Matrix (Fin 2) (Fin 2) F) (v : Fin 2 → F) :
    firstCols (cat3 A v) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [firstCols, cat3]

end D

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair

theorem GlobalTheory.CompanionTheory.GL2DualWhittakerPair.pullback_schwartz_bruhat_M2 : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (Φ : Matrix (Fin 2) (Fin 3) F → ℂ), Φ ∈ LFS.SB F → ∀ h z : GL (Fin 2) F, SB2 (Pf Φ h z) := by
  intro F _ _ _ _ _ _ Φ hΦ h z
  obtain ⟨hl, hc⟩ := hΦ
  set A : GL (Fin 2) F := z⁻¹ with hA
  set B : GL (Fin 2) F := tinv h with hB
  set v : Fin 2 → F := A.val *ᵥ e1 with hv
  have hι : Continuous fun M : Matrix (Fin 2) (Fin 2) F => cat3 (A.val * M * B.val) v :=
    continuous_block_concatenation _ _ _
  refine ⟨hl.comp_continuous hι, ?_⟩
  let q : Matrix (Fin 2) (Fin 3) F → Matrix (Fin 2) (Fin 2) F :=
    fun X => (A⁻¹).val * firstCols X * (B⁻¹).val
  have hq : Continuous q :=
    (continuous_const.matrix_mul continuous_firstCols).matrix_mul continuous_const
  refine HasCompactSupport.of_support_subset_isCompact (hc.isCompact.image hq) ?_
  intro M hM
  refine ⟨cat3 (A.val * M * B.val) v, subset_tsupport _ hM, ?_⟩
  have h1 : (A⁻¹).val * A.val = 1 := by rw [← Units.val_mul]; simp
  have h2 : B.val * (B⁻¹).val = 1 := by rw [← Units.val_mul]; simp
  simp only [q, first_columns_concatenation]
  calc (A⁻¹).val * (A.val * M * B.val) * (B⁻¹).val
      = ((A⁻¹).val * A.val) * M * (B.val * (B⁻¹).val) := by simp only [Matrix.mul_assoc]
    _ = M := by rw [h1, h2]; simp
