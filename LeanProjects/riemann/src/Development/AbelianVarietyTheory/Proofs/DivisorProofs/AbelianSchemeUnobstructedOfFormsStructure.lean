import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftAbelianSchemeSquareZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicationLiftsSquareZeroSmoothLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickening
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsAbelianSchemeSmoothLiftNilpotent
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem unobDim_of_formSt : FormSt → PrimitiveExtendedDegTwoVanish → AxesVanishingExtendedDegOne → UnobDim := by
  intro hF hP hA R _ I hI R₀ _ π hπ hk A₀ _ g hab hsm
  obtain ⟨X, i, hpb, hsmX⟩ := GlobalTheory.T.exists_smooth_lift_abelian_scheme_square_zero hF hP R R₀ I hI π hπ hk A₀ g hab hsm
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hk]; exact hI⟩
  have h1 : (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀).left ≫ A₀.hom = 𝟙 _ := by
    simpa using Over.w (1 : Over.mk (𝟙 (Sp R₀)) ⟶ A₀)
  obtain ⟨e, he, he'⟩ := GlobalTheory.SecLift.exists_section_lift R R₀ π hπ hnil X A₀ i hpb hsmX _ h1
  have P := IsPullback.of_hasPullback X.hom X.hom
  have w : ((fst A₀ A₀).left ≫ i) ≫ X.hom = ((snd A₀ A₀).left ≫ i) ≫ X.hom := by
    simp only [Category.assoc, hpb.w]
    rw [← Category.assoc, ← Category.assoc, Over.w (fst A₀ A₀), Over.w (snd A₀ A₀)]
  let l : (A₀ ⊗ A₀).left ⟶ (X ⊗ X).left := P.lift _ _ w
  have l1 : l ≫ (fst X X).left = (fst A₀ A₀).left ≫ i := P.lift_fst _ _ w
  have l2 : l ≫ (snd X X).left = (snd A₀ A₀).left ≫ i := P.lift_snd _ _ w
  obtain ⟨m, hm⟩ := GlobalTheory.T.multiplication_lifts_square_zero_smooth_lift hF hA R R₀ I hI π hπ hk A₀ g hab hsm X i hpb hsmX e he he' l l1 l2
  obtain ⟨G, hG, hab'⟩ := GlobalTheory.LiftGroupLaw.exists_grpObj_isAbelianScheme R R₀ π hπ hnil A₀ hab X i hpb hsmX e he he'
    l l1 l2 m hm
  exact ⟨X, G, i, hG, hab'⟩

end GlobalTheory.Obs
