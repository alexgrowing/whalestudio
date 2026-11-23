import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfGaloisFixed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FinDescent

theorem galoisFixed_point_of_finite : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V], IsIntegrallyClosed V → ∀ (N : Over (Sp V)), IsFinite N.hom → ∀ (nb : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ N), (∀ σ : AlgebraicClosure (FractionRing V) ≃ₐ[FractionRing V] AlgebraicClosure (FractionRing V), spMap σ.toAlgHom.toRingHom ≫ nb.left = nb.left) → ∃ s : 𝟙_ (Over (Sp V)) ⟶ N, nb = toUnit _ ≫ s := by
  first
  | exact @_root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed
  | exact _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed
  | (apply _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> assumption)
  | (intros; apply _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GaloisFixedSectionExtension.exists_section_of_galoisFixed ..)

end GlobalTheory.FinDescent
