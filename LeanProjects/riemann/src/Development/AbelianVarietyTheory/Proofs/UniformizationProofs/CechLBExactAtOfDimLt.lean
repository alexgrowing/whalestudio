import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCoverOfIsProjByOfInfinite
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCoversStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbLaw

theorem cechLB_exactAt_of_dim_lt :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (Y : Scheme.{0}) [IsIntegral Y] (f : Y ⟶ Spec (CommRingCat.of K)) (g : ℕ) (M : LB Y), SmoothOfRelativeDimension g f → IsProjBy f → IsSeparated f → M.IsLB → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ∀ n, g < n → (cechLB f M D).ExactAt n := by
  intro K _ _ Y _ f g M hf hp hs hM κ _ _ D hD hc n hn
  obtain ⟨E, hE, hEc⟩ := GlobalTheory.AffineCover.exists_cover_of_isProjBy K Y f g hf hp
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_cechLB_homology_equiv_of_affine_covers K Y f M κ D (Fin (g + 1)) E hM hs hD hc hE hEc n
  have hz : IsZero ((cechLB f M E).X n) := isZero_cechLB_X f M E (by simpa using hn)
  have hE0 : IsZero ((cechLB f M E).homology n) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
      (HomologicalComplex.ExactAt.of_isZero hz)
  have : Subsingleton ((cechLB f M E).homology n) := ModuleCat.isZero_iff_subsingleton.1 hE0
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (ModuleCat.isZero_iff_subsingleton.2 e.toEquiv.subsingleton)

end GlobalTheory.AbLaw
