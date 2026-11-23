import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.ABoundOfDescends
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.ExistsDescends

open UpperTheory.V UpperTheory.V.PropA NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.PropA.descends :
    ∀ (l : ℕ) [Fact l.Prime] (L₀ : Type) [Field L₀] [NumberField L₀], HasMuQ l L₀ →
      ∀ γ : G L₀ (AlgebraicClosure L₀), IsGen l ⊤ γ → Descends l L₀ γ := by
  intro l _ L₀ _ _ hmu γ hγ e he m L₁ _ _ _ hL
  have hne : (e : ℤ) ≠ 0 := by
    have : 0 < e := he
    exact_mod_cast this.ne'
  exact step0 hmu hγ hne m L₁ hL
