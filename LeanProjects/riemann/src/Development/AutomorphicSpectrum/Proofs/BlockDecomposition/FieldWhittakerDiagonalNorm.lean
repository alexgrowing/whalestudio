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
namespace GlobalTheory.CompanionTheory.FexTheta

theorem whittaker_diagonal_norm_field : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ¬ L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
    L.W (dg2 (nv v κ) 1 * g) = cW L κ * mp (nv v κ) (1 / 2) * locI L g κ := by
  intro K _ _ h2 c v m hok hsp g κ
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
    have : (((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) : Qv v → Circle) = fun x => (GP.psiF v x)⁻¹ := by
      funext x; exact AddChar.inv_apply' _ _
    rw [this]
    exact hstd.1.inv
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.mpr hstd.2.1
  cases m with
  | @sp w₁ w₂ i₁ i₂ Φ => exact absurd trivial hsp
  | @ns w i σ η Φ =>
    haveI := i
    obtain ⟨hu, hσ, hη, hΦ⟩ := hok
    have hN : ((nv v κ : (Qv v)ˣ) : Qv v) = Algebra.norm (Qv v) ((atW w κ : (Kv K w)ˣ) : Kv K w) := by
      have h1 := GlobalTheory.T.local_norm_at_inert_place K h2 v w hu (κ : K)
      have h3 := GlobalTheory.T.local_component_rational_idele v (Units.map (Algebra.norm ℚ : K →* ℚ) κ)
      show ((Ad3.R.lc v (pri (Units.map (Algebra.norm ℚ : K →* ℚ) κ)) : (Qv v)ˣ) : Qv v) = Algebra.norm (Qv v) (algebraMap K (Kv K w) (κ : K))
      rw [h3, h1]
      rfl
    have key := GlobalTheory.T.field_weil_action_diagonal (Qv v) _ hχc hχ1 (Kv K w)
      (GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl K h2 v w i σ hσ)
      (continuous_adicCompletionMap v w) σ hσ η hη _ Φ hΦ (atW w κ) (nv v κ) hN g 1
    rw [one_mul] at key
    have hWc : ∀ h : GL (Fin 2) (Qv v), (LM.ns w σ η Φ : LM c v).W h =
        GL2LocalData.piE (Kv K w) (GP.psiF v)⁻¹ σ η (localChar c w) h Φ 1 := by
      intro h
      rfl
    rw [hWc, key]
    rfl

end GlobalTheory.CompanionTheory.FexTheta
