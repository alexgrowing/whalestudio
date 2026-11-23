import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftToPrimeLocalization
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_to_prime_localization : ∀ (U X : Scheme.{0}) (j : U ⟶ X) [IsOpenImmersion j] (R : Type) [CommRing R] (ξ : Sp R ⟶ X)
    (K' : Type) [Field K'] (χ : R →+* K') (yy : Sp K' ⟶ U), spMap χ ≫ ξ = yy ≫ j →
    ∀ (q : Ideal R) [q.IsPrime], RingHom.ker χ = q →
      ∃ yq : Sp (Localization.AtPrime q) ⟶ U, spMap (algebraMap R (Localization.AtPrime q)) ≫ ξ = yq ≫ j := by
  first | exact @GlobalTheory.spec_factor_localization_of_field_point | exact GlobalTheory.spec_factor_localization_of_field_point | (intros; apply GlobalTheory.spec_factor_localization_of_field_point <;> assumption)
