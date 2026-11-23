import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionEquationGlobal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FieldWeilActionLocallyConstantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionTorusEquivariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionLocallyConstantStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver

namespace GlobalTheory.CompanionTheory.ThetaStab

theorem val_stab : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → ∀ g₀ : GL (Fin 2) (Qv v), L.plus g₀ → ∃ U ∈ nhds g₀, ∀ g ∈ U, ∀ (τ : (Qv v)ˣ) (ξ : K),
    (L.tw τ).val g ξ = (L.tw τ).val g₀ ξ := by
  intro K _ _ h2 c v L hok g₀ hp
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.RankinQ.isStd_local v
  have hψ := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.continuous_charInv (GP.psiF v) hstd.1
  have hψ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.2 hstd.2.1
  cases L with
  | @sp w₁ w₂ h₁ h₂ Φ =>
    obtain ⟨_, hl, hc⟩ := hok
    obtain ⟨U, hU, hUe⟩ := GlobalTheory.T.split_weil_action_locally_constant (Qv v) (GP.psiF v)⁻¹ hψ hψ1 (cAt c v w₁)
      (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_cAt c v w₁) Φ ⟨hl, hc⟩ g₀
    refine ⟨U, hU, fun g hg τ ξ => ?_⟩
    have e := fun h : GL (Fin 2) (Qv v) => GlobalTheory.T.split_weil_action_torus_equivariant (Qv v) (GP.psiF v)⁻¹ hψ hψ1 (cAt c v w₁) h Φ τ
      (dg1 v w₁ ξ, dg1 v w₂ ξ)
    simp only [LM.tw, LM.val]
    rw [e g, e g₀, hUe g hg]
  | @ns w h σ η Φ =>
    obtain ⟨hu, hσ, hη, hΦ⟩ := hok
    obtain ⟨U, hU, hUe⟩ := GlobalTheory.T.field_weil_action_locally_constant (Qv v) (GP.psiF v)⁻¹ hψ hψ1 (Kv K w)
      (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.places_nonsplit h2 v w hu) (_root_.continuous_algebraMap (Qv v) (Kv K w)) σ hσ η hη
      (localChar c w) (GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.isUnit1_localCharK c w) Φ hΦ g₀ hp
    refine ⟨U, hU, fun g hg τ ξ => ?_⟩
    exact congrFun (hUe g hg) _

end GlobalTheory.CompanionTheory.ThetaStab
