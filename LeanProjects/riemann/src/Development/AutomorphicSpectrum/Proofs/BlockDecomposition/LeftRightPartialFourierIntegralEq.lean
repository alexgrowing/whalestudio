import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralGL2EqFiberCoordinates
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GodementJacquetMinusOne
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.GL2DualWhittakerPair.CellFubini

section D

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem integrable_Ff {ψ : AddChar F Circle} (hψ : IsStd ψ) {f : GL (Fin 2) F → ℂ}
    (hf : Integrable f (LFS.hG ψ)) :
    Integrable (GJTwo.Ff f) (GJTwo.cM ψ) ∧
      ∫ g, f g ∂LFS.hG ψ = ∫ p, GJTwo.Ff f p ∂GJTwo.cM ψ := by
  have hU : MeasurableSet (GJTwo.cellU F) := GJTwo.isOpen_cellU.measurableSet
  have hmap := GJTwo.hG_eq_map GJHaar.gjm1 hψ
  rw [hmap] at hf
  have hs := hf.aestronglyMeasurable
  constructor
  · rw [integrable_map_measure hs GJTwo.measurable_cellPsi.aemeasurable, GJTwo.cellNu,
      integrable_withDensity_iff_integrable_smul GJTwo.measurable_cellD] at hf
    rw [GJTwo.Ff_eq, integrable_indicator_iff hU]
    exact hf
  · rw [hmap, integral_map GJTwo.measurable_cellPsi.aemeasurable hs, GJTwo.cellNu,
      integral_withDensity_eq_integral_smul GJTwo.measurable_cellD, GJTwo.Ff_eq,
      integral_indicator hU]
    rfl

theorem integral_fibre {ψ : AddChar F Circle} {G : (Fin 2 → F) × F × F → ℂ}
    (hG : Integrable G (GJTwo.cM ψ)) :
    ∫ p, G p ∂GJTwo.cM ψ =
      ∫ r, ∫ y, ∫ x, G (r, x, y) ∂selfDualMeasure ψ ∂selfDualMeasure ψ ∂LFS.vol2 ψ := by
  haveI : SigmaFinite (LFS.vol2 ψ) := by unfold LFS.vol2; infer_instance
  rw [GJTwo.cM] at hG
  rw [GJTwo.cM, integral_prod _ hG]
  refine integral_congr_ae ?_
  filter_upwards [hG.prod_right_ae] with r hr
  exact integral_prod_symm _ hr

theorem Ff_cell {ψ : AddChar F Circle} (A : GL (Fin 2) F → ℂ)
    (P : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F → ℂ)
    (hA : ∀ u z, A (uni2 u * z) = (ψ u : ℂ) * A z)
    (hP : ∀ u z M, P (uni2 u * z) M = P z ((uni2 (-u)).val * M))
    (B : (Matrix (Fin 2) (Fin 2) F → ℂ) → ℂ) (r : Fin 2 → F) (x y : F) (h : ¬ (y = 0 ∨ r 1 = 0)) :
    GJTwo.Ff (fun z => A z * B (P z)) (r, x, y) =
      (A (dg2 (Units.mk0 y (fun e => h (Or.inl e))) 1 * hr r) *
          (((modulus y : ℝ) ^ (-2 : ℤ) : ℝ) : ℂ)) *
        ((ψ x : ℂ) * B (fun M => P (dg2 (Units.mk0 y (fun e => h (Or.inl e))) 1 * hr r)
          ((uni2 (-x)).val * M))) := by
  have hP' : P (uni2 x * (dg2 (Units.mk0 y (fun e => h (Or.inl e))) 1 * hr r)) =
      fun M => P (dg2 (Units.mk0 y (fun e => h (Or.inl e))) 1 * hr r) ((uni2 (-x)).val * M) :=
    funext fun M => hP _ _ M
  simp only [GJTwo.Ff, dif_neg h]
  rw [mul_assoc (uni2 x), hA, hP']
  ring

end D

theorem core : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → (∀ p : Matrix (Fin 2) (Fin 2) F → ℂ, SB2 p → ∫ u, (ψ u : ℂ) * Lpart ψ (fun M => p ((uni2 (-u)).val * M)) ∂selfDualMeasure ψ = ∫ t, (ψ t : ℂ) * Rpart ψ (fun M => p ((uni2 (-t)).val * M)) ∂selfDualMeasure ψ) → ∀ (A : GL (Fin 2) F → ℂ) (P : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F → ℂ), (∀ u z, A (uni2 u * z) = (ψ u : ℂ) * A z) → (∀ u z M, P (uni2 u * z) M = P z ((uni2 (-u)).val * M)) → (∀ z, SB2 (P z)) → Integrable (fun z => A z * Lpart ψ (P z)) (LFS.hG ψ) → Integrable (fun z => A z * Rpart ψ (P z)) (LFS.hG ψ) → ∫ z, A z * Lpart ψ (P z) ∂LFS.hG ψ = ∫ z, A z * Rpart ψ (P z) ∂LFS.hG ψ := by
  intro F _ _ _ _ _ _ ψ hψ hyp A P hA hP hS h1 h2
  obtain ⟨i1, q1⟩ := integrable_Ff hψ h1
  obtain ⟨i2, q2⟩ := integrable_Ff hψ h2
  rw [q1, q2, integral_fibre i1, integral_fibre i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases h : y = 0 ∨ r 1 = 0
  · simp only [GJTwo.Ff, dif_pos h]
  · simp only [Ff_cell A P hA hP (Lpart ψ) r _ y h, Ff_cell A P hA hP (Rpart ψ) r _ y h]
    rw [integral_const_mul, integral_const_mul, hyp _ (hS _)]

end GlobalTheory.CompanionTheory.GL2DualWhittakerPair.CellFubini
