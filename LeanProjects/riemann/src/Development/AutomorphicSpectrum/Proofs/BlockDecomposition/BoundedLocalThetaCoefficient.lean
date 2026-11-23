import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCoefficientMeasurableBounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLocalThetaBoundedIntegral

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

namespace GlobalTheory.CompanionTheory.FexBound

theorem bounded : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K), ∃ C : ℝ, ∀ x, ‖fL L g ξ x‖ ≤ C := by
  intro K _ _ _ c v L hok g ξ
  cases L with
  | @sp w₁ w₂ h₁ h₂ Φ =>
    obtain ⟨_, hl, hc⟩ := hok
    have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.RankinQ.isStd_local v
    have hχc := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.continuous_charInv (GP.psiF v) hstd.1
    have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.2 hstd.2.1
    have hf := (GlobalTheory.CompanionTheory.SplitPi.sPiRep (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) (cAt c v w₂)
      (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₁) (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₂) Φ ⟨hl, hc⟩ 1 g).2
    obtain ⟨B, hB⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2
    refine ⟨B, fun x => ?_⟩
    unfold fL
    rw [norm_mul, GlobalTheory.CompanionTheory.CtMeas.norm_ct, one_mul]
    change ‖GL2LocalData.piS (GP.psiF v)⁻¹ (cAt c v w₁) g (fun y => Φ (y * ((x : Qv v), ((x⁻¹ : (Qv v)ˣ) : Qv v))))
      (dg1 v w₁ ξ, dg1 v w₂ ξ)‖ ≤ B
    rw [GlobalTheory.T.split_weil_action_torus_equivariant (Qv v) (GP.psiF v)⁻¹ hχc hχ1 (cAt c v w₁) g Φ x]
    exact hB _
  | @ns w h σ η Φ =>
    refine ⟨‖(LM.ns w σ η Φ : LM c v).val g ξ‖, fun x => ?_⟩
    unfold fL
    rw [norm_mul, GlobalTheory.CompanionTheory.CtMeas.norm_ct, one_mul]
    exact le_rfl

end GlobalTheory.CompanionTheory.FexBound
