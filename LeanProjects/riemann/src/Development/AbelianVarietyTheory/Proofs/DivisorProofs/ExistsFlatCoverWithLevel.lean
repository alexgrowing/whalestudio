import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatLevelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeRankTwo
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.RealMult.exists_faithfullyFlat_level :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F) (N : ℕ), 1 ≤ N →
      ∀ (R : Type) [CommRing R], IsUnit (N : R) → ∀ X : Obj F 𝔠 (Sp R),
        ∃ (R' : Type) (_ : CommRing R') (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
          σ.FaithfullyFlat ∧ X'.IsPullBy X (spMap σ) φ ∧ Nonempty (X'.Level N) :=
  GlobalTheory.RealMult.exists_faithfullyFlat_level_of GlobalTheory.RealMult.torsion_free_rank_two
