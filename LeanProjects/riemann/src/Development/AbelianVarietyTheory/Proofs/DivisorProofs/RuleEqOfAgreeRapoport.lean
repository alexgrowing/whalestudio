import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RuleEqOfAgreeRapoportOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatCoverWithLevel
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.RealMult.rule_eq_of_agree_rapoport : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀]
  (k : ℕ) (r s : Rule (trivialObjectCondition 𝔠) R₀ k),
  (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)), X.IsRapoport → ∀ δ : X.DetGen,
    r.val R X trivial δ = s.val R X trivial δ) → r = s :=
  GlobalTheory.RealMult.rule_eq_of_agree_rapoport_of_level GlobalTheory.RealMult.exists_faithfullyFlat_level
