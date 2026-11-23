import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismDescendsToAlgebraic
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_holUnif_square : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∃ (n : ℕ) (L' : LB (A ⊗ A).left) (v : HolUnif (A ⊗ A) L' n) (M₁ M₂ : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsAbelianScheme (A ⊗ A) ∧ (∀ w, u.ex (M₁ w) = v.ex w ≫ fst A A) ∧ (∀ w, u.ex (M₂ w) = v.ex w ≫ snd A A) ∧ (∀ w, u.ex ((M₁ + M₂) w) = v.ex w ≫ μ[A]) ∧ (∀ l : v.Λ, M₁ l ∈ u.Λ) ∧ ∀ l : v.Λ, M₂ l ∈ u.Λ := by
  intro A _ g L u hA
  have hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hg := GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u
  obtain ⟨n, hn⟩ := GlobalTheory.AbelianDim.exists_relDim ℂ (A ⊗ A) hAA
  obtain ⟨L', ⟨v⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif (A ⊗ A) n hAA hn
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u hg
  obtain ⟨M₁, hM₁, hΛ₁, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom (A ⊗ A) A hAA hA L' L n g v u h₁ h₂
    (fst A A) inferInstance
  obtain ⟨M₂, hM₂, hΛ₂, -⟩ := GlobalTheory.HomLinear.exists_linear_of_isMonHom (A ⊗ A) A hAA hA L' L n g v u h₁ h₂
    (snd A A) inferInstance
  refine ⟨n, L', v, M₁, M₂, hAA, hM₁, hM₂, fun w => ?_, fun l => hΛ₁ l l.2, fun l => hΛ₂ l l.2⟩
  rw [LinearMap.add_apply, u.ex_add, hM₁, hM₂, Hom.mul_def, ← comp_lift, lift_fst_snd, Category.comp_id]

end GlobalTheory.CechPer
