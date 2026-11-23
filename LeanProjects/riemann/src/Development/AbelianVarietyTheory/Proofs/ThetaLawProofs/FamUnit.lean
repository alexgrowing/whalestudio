import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsUnitThetaKeyRuleSmoothBase
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsValueOfGeneric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyFamUnit

theorem famUnit : ∀ κ : Rule, Funct κ → UnitSp κ → FamUnit κ := by
  intro κ hF hU S _ _ _ _ _ y
  obtain ⟨u, hu⟩ := GlobalTheory.KeySmoothBase.exists_unit_normal (κ := κ) hF hU S y
  exact ⟨u, GlobalTheory.KeySpec.isValue_of_generic κ hF hU S y u fun K _ _ f x hf hx =>
    hu K f x ((RingHom.injective_iff_ker_eq_bot f).1 hf) hx⟩

end GlobalTheory.KeyFamUnit
