import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed.HeckeRelations

private theorem conv_smul_right {X : Type} [Group X] (K : Subgroup X) (f f' : X → ℂ) (c : ℂ) :
    conv K f (c • f') = c • conv K f f' := by
  funext g
  show ∑ᶠ x : X ⧸ K, f x.out * (c • f') (x.out⁻¹ * g) = c • ∑ᶠ x : X ⧸ K, f x.out * f' (x.out⁻¹ * g)
  rw [smul_finsum]
  refine finsum_congr fun x => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end UpperTheory.Gal.W2.Seed.HeckeRelations
