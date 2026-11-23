import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRuleUnitObjOfCovers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatLevelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeRankTwo
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.RuleDescend

theorem exists_rule_unitObj :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
  ∀ (R₀ : Type) [CommRing R₀] (k : ℕ) (r₀ : Rule (rapObj 𝔠) R₀ k) (r : Rule (levObj 𝔠 N) R₀ k),
  (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : levObj 𝔠 N R X)
    (hX : X.IsRapoport) (δ : X.DetGen), r.val R X h δ = r₀.val R X hX δ) →
  ∃ r' : Rule (unitObj 𝔠 N) R₀ k,
    (∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : levObj 𝔠 N R X) (δ : X.DetGen),
      r'.val R X h.1 δ = r.val R X h δ) ∧
    ∀ (R : Type) [CommRing R] [Algebra R₀ R] (X : Obj F 𝔠 (Sp R)) (h : IsUnit ((N : ℕ) : R))
      (hX : X.IsRapoport) (δ : X.DetGen), r'.val R X h δ = r₀.val R X hX δ :=
  exists_rule_unitObj_of_covers (exists_faithfullyFlat_level_of torsion_free_rank_two)

end GlobalTheory.RealMult.RuleDescend
