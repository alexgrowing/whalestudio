import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

namespace GlobalTheory.AmpleDescent

theorem relAmple_of_faithfullyFlat : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] [Algebra R R'] [Module.FaithfullyFlat R R'] (B : Over (Sp R)) (B' : Over (Sp R')) [GrpObj B] [GrpObj B'] (φ : B'.left ⟶ B.left) (L : LB B.left) (L' : LB B'.left), IsAbelianScheme B → IsGrpPullback B' B (spMap (algebraMap R R')) φ → L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → RelAmple B' L' → RelAmple B L := by
  intro R R' _ _ _ _ _ _ _ B B' _ _ φ L L' hB h hL hL' hw hA
  have : Flat (Out.specOf (algebraMap R R')) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (Out.specOf (algebraMap R R')) :=
    ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := R')⟩
  have : IsProper B.hom := hB.proper
  have : IsProper B'.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) h.1 inferInstance
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : QuasiSeparatedSpace B.left := quasiSeparatedSpace_of_quasiSeparated B.hom
  refine (relAmple_iff_isAmpleLB_of_isAffine B hL).2 (isAmpleLB_of_pull (algebraMap R R') h.1 hL ?_)
  exact (isAmpleLB_of_relAmple_of_isAffine B' hL' hA).of_lbIso (LB.isLB_pull hL φ) hw.symm

end GlobalTheory.AmpleDescent
