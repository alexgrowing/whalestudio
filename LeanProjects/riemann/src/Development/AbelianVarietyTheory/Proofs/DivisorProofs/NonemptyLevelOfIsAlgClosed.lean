import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLevelOfTorsionBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeRankTwo
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.RealMult

theorem nonempty_level_of_isAlgClosed :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ) (K : Type) [Field K] [IsAlgClosed K],
    (N : K) ≠ 0 → ∀ X : Obj F 𝔠 (Sp K), Nonempty (X.Level N) :=
  nonempty_level_of_torsion_basis torsion_free_rank_two

end GlobalTheory.RealMult
