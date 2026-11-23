import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComponentRationalIdeleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldWeilActionDiagonalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormAtInertPlaceStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.ValZeroNs

theorem val_zero_dg : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
    L.ok → ¬ L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
      L.val (dg2 (nv v κ) 1 * g) 0 = c0 L κ * mp (nv v κ) (1 / 2) * L.val g 0 := by
  intro K _ _ h2 c v L hok hsp g κ
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
    have : (((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) : Qv v → Circle) = fun x => (GP.psiF v x)⁻¹ := by
      funext x; exact AddChar.inv_apply' _ _
    rw [this]
    exact hstd.1.inv
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.mpr hstd.2.1
  cases L with
  | @sp w₁ w₂ i₁ i₂ Φ => exact absurd trivial hsp
  | @ns w i σ η Φ =>
    haveI := i
    obtain ⟨hU, hσ, hη, hΦ⟩ := hok
    have hN : ((nv v κ : (Qv v)ˣ) : Qv v) = Algebra.norm (Qv v) ((atW w κ : (Kv K w)ˣ) : Kv K w) := by
      have e1 : ((nv v κ : (Qv v)ˣ) : Qv v) =
          (((Units.map (Algebra.norm ℚ : K →* ℚ) κ : ℚˣ) : ℚ) : Qv v) := GlobalTheory.T.local_component_rational_idele v _
      have e2 := GlobalTheory.T.local_norm_at_inert_place K h2 v w hU (κ : K)
      rw [e1]
      exact e2.symm
    have h := GlobalTheory.T.field_weil_action_diagonal (Qv v) _ hχc hχ1 (Kv K w)
      (GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl K h2 v w i σ hσ)
      (continuous_adicCompletionMap v w) σ hσ η hη _ Φ hΦ (atW w κ) (nv v κ) hN g
      (algebraMap K (Kv K w) 0)
    have e0 : algebraMap K (Kv K w) 0 * ((atW w κ : (Kv K w)ˣ) : Kv K w) = algebraMap K (Kv K w) 0 := by
      rw [map_zero, zero_mul]
    rw [e0] at h
    exact h

end GlobalTheory.CompanionTheory.ValZeroNs
