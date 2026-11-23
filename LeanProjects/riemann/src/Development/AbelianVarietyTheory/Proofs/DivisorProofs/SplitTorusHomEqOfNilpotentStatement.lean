import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomEqOfNilpotent
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorus_hom_eq_of_bcMap_comp_eq : ∀ (A κ : Type) [CommRing A] [IsLocalRing A] [CommRing κ] (π : A →+* κ), Function.Surjective π → IsNilpotent (RingHom.ker π) → ∀ (X : Type) [AddCommGroup X] (H : Over (Sp A)) [GrpObj H] [IsCommMonObj H] (i₁ i₂ : splitTorus (Sp A) X ⟶ H), IsMonHom i₁ → IsMonHom i₂ → GlobalTheory.SplitTorus.bcMap (spMap π) X ≫ i₁.left = GlobalTheory.SplitTorus.bcMap (spMap π) X ≫ i₂.left → i₁ = i₂ := by
  first | exact @GlobalTheory.splitTorus_hom_eq_of_nilpotent | exact GlobalTheory.splitTorus_hom_eq_of_nilpotent | (intros; apply GlobalTheory.splitTorus_hom_eq_of_nilpotent <;> assumption)
