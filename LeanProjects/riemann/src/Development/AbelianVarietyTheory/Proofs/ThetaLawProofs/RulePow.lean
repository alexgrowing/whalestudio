import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRulePowComplexStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyDataDescendCountableSubringsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsKeyPow
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleExistsOfAlgebraicInvariants

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyCl

theorem rule_pow : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → ThetaOne κ → ∀ (K : Type) [Field K] [CharZero K]
    (x y : KeyIn K) (j : ℕ), GlobalTheory.KeyPow.IsKeyPow y x j → κ K y = κ K x ^ j := by
  intro κ hH hF hT K _ _ x y j hp
  have hj : 1 ≤ j := by
    obtain ⟨_, hg, -⟩ := hp
    have := y.g_pos
    rcases Nat.eq_zero_or_pos j with rfl | h
    · omega
    · exact h
  obtain ⟨K₀, x₀, hK₀, hx₀⟩ := (GlobalTheory.T.keyData_descend_countable_subrings GlobalTheory.firstFiveLaws.1).2 K x
  obtain ⟨σ⟩ := GlobalTheory.KeyHouse.nonempty_ringHom_complex K₀
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.KeyPow.exists_isKeyPow _ x₀ j hj
  obtain ⟨x₁, hx₁⟩ := GlobalTheory.KeyPow.exists_keyPB_ring x₀ σ
  obtain ⟨y₁, hy₁⟩ := GlobalTheory.KeyPow.exists_isKeyPow _ x₁ j hj
  have e₀ := GlobalTheory.KeyPow.keyPB_of_isKeyPow _ _ _ x₀ y₀ x y j hx₀ hy₀ hp
  have e₁ := GlobalTheory.KeyPow.keyPB_of_isKeyPow _ _ _ x₀ y₀ x₁ y₁ j hx₁ hy₀ hy₁
  have e := congrArg Units.val (GlobalTheory.T.thetaKeyRule_pow_complex κ hH hT x₁ y₁ j hy₁)
  rw [Units.val_pow_eq_pow_val, hF _ _ σ y₀ y₁ e₁, hF _ _ σ x₀ x₁ hx₁, ← map_pow] at e
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hF _ _ _ y₀ y e₀, hF _ _ _ x₀ x hx₀, ← map_pow, σ.injective e]

end GlobalTheory.KeyCl
