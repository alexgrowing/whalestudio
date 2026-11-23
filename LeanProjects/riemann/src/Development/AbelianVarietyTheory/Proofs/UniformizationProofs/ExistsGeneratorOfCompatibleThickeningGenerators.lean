import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OpenEqTopOfContainsSpecialPartUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionLinearCombinationOfCompatibleThickeStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Unif

theorem exists_gen_of_thick : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : Over (Spec (CommRingCat.of R))), Smooth Y.hom → IsProjBy Y.hom → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (Y.left ⟶ W)) (ε : K → ℤ) (φ' : ∀ e, K → ((thickObj R I e Y).left ⟶ W)), L.IsLB → (∀ e k, pullback.fst Y.hom (thick R I e) ≫ φ k = φ' e k) → ∀ f : ∀ e, LB.Gen (LB.LinComb L (φ' e) ε), (∀ e, (f e).IsGen) → (∀ e z J, Good L z J → val (f (e + 1)) (thickMap R I e Y) z J = val (f e) (𝟙 _) z J) → ∃ u : LB.Gen (LB.LinComb L φ ε), u.IsGen ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e Y).left) (z : Z) (J), Good L z J → val u (r ≫ pullback.fst Y.hom (thick R I e)) z J = val (f e) r z J := by
  intro R _ _ I hI Y hs hp W L K _ φ ε φ' hL hφ f hf hc
  obtain ⟨s, hsv⟩ := GlobalTheory.T.exists_section_linearCombination_of_compatible_thickenings R I hI Y hs hp W L K φ ε φ' hL hφ (fun e => genSec (f e) (hf e))
    (fun e z J hJ => (sval_genSec _ _ _ z hJ).trans
      ((congrArg Units.val (hc e z J hJ)).trans (sval_genSec _ _ _ z hJ).symm))
  have : IsProper Y.hom := GlobalTheory.AbLaw.isProper_of_isProjBy _ _ _ hp
  have top : nonzeroLocus s = ⊤ :=
    eq_top_of_special_part R I (IsAdicComplete.le_jacobson_bot I) Y _ fun z => by
      choose J hJ using fun ψ : (thickObj R I 0 Y).left ⟶ W => exists_chart hL (ψ z)
      have h1 := hsv 0 _ (𝟙 _) z J hJ
      rw [Category.id_comp, sval_genSec _ _ _ z hJ] at h1
      refine (TwistZero.mem_nonzeroLocus_iff s (pullback.fst Y.hom (thick R I 0)) z hJ).2 ?_
      exact (congrArg IsUnit h1).mpr (Units.isUnit _)
  have hu : ∀ j, IsUnit (s.f j) := fun j => Y.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL s y j hy
    exact (congrArg IsUnit ((gs_eq (𝟙 Y.left) y (LB.wchart L φ j) hy _).symm.trans e)).mpr
      ((Units.isUnit _).mul ((TwistZero.mem_nonzeroLocus_iff s (𝟙 _) y hJ).1 (by rw [top]; trivial)))
  refine ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j), fun e Z r z J hJ => Units.ext ?_⟩
  exact (gs_unit _ z _ (hJ.mem φ _) _).symm.trans ((hsv e Z r z J hJ).trans (sval_genSec _ _ r z hJ))

end GlobalTheory.Unif
