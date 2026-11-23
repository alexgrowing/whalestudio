import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenLocalFactorization
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitObj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_open_local_factorization : ∀ (M : Scheme.{0}) (W : M.Opens) (hW : IsAffineOpen W) (R : Type) [CommRing R] (b : Sp R ⟶ M) (p : PrimeSpectrum R),
    b p ∈ W → ∃ (f : R) (g : Γ(M, W) →+* Localization.Away f), f ∉ p.asIdeal ∧
      spMap g ≫ hW.fromSpec = spMap (algebraMap R (Localization.Away f)) ≫ b := by
  first | exact @GlobalTheory.affine_factor_basicOpen_affineOpen | exact GlobalTheory.affine_factor_basicOpen_affineOpen | (intros; apply GlobalTheory.affine_factor_basicOpen_affineOpen <;> assumption)
