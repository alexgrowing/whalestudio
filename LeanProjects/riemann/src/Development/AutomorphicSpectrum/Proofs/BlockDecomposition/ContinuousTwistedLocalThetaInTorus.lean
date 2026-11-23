import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionTorusEquivariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedRepresentationHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.TwistCont

theorem val_tw_continuous : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
    L.ok → ∀ g₀ : GL (Fin 2) (Qv v), L.plus g₀ → ∀ ξ : K,
      Continuous (fun τ : (Qv v)ˣ => (L.tw τ).val g₀ ξ) := by
  intro K _ _ _ c v L hL g₀ _ ξ
  cases L with
  | ns w σ η Φ => exact continuous_const
  | sp w₁ w₂ Φ =>
    obtain ⟨-, hlc, hcs⟩ := hL
    have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
    obtain ⟨hχc, hχ1, -⟩ :=
      (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
    have hf := (GlobalTheory.CompanionTheory.SplitPi.piS_mem hχc hχ1 (cAt c v w₁)
      (show Φ ∈ GL2LocalData.SBE (Qv v × Qv v) from ⟨hlc, hcs⟩) g₀).1
    have hτ : Continuous (fun τ : (Qv v)ˣ =>
        (dg1 v w₁ ξ, dg1 v w₂ ξ) * ((τ : Qv v), ((τ⁻¹ : (Qv v)ˣ) : Qv v))) :=
      continuous_const.mul (Units.continuous_val.prodMk (Units.continuous_val.comp continuous_inv))
    have e : (fun τ : (Qv v)ˣ => ((LM.sp w₁ w₂ Φ : LM c v).tw τ).val g₀ ξ) = fun τ : (Qv v)ˣ =>
        GL2LocalData.piS (GP.psiF v)⁻¹ (cAt c v w₁) g₀ Φ
          ((dg1 v w₁ ξ, dg1 v w₂ ξ) * ((τ : Qv v), ((τ⁻¹ : (Qv v)ˣ) : Qv v))) := by
      funext τ
      exact GlobalTheory.CompanionTheory.SplitTorus.piS_torus (Qv v) _ hχc hχ1 (cAt c v w₁) g₀ Φ τ _
    rw [e]
    exact hf.continuous.comp hτ

end GlobalTheory.CompanionTheory.TwistCont
