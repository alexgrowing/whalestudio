import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteClosedSubschemeRepresentsKernelAmpleStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatOfIsFiniteOfFlatLocalizationMaximalStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemKernelOfLineBundleBaseChangeRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LineBundleKernelFlatOfFiniteNoetherianLocalStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubeProjectiveAbelianSchemeAffineBase
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelFlat

theorem kernelFiniteFlat : Laws → GlobalTheory.Published.KernelFiniteFlatSt := by
  intro hLaw V _ _ A _ hA L hL ha
  obtain ⟨H, j, hj, hfin, hH⟩ := GlobalTheory.T.exists_finite_closed_subscheme_represents_kernel_ample hLaw.globalFns V A hA L hL ha
  refine ⟨H, j, hj, hfin, GlobalTheory.T.flat_of_isFinite_of_flat_at_maximal V H hfin fun m _ => ?_, hH⟩
  let f := spMap (algebraMap V (Localization.AtPrime m))
  have hA' : IsAbelianScheme ((Over.pullback f).obj A) := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have : IsCommMonObj ((Over.pullback f).obj A) := hA'.comm
  have hP : IsProjBy ((Over.pullback f).obj A).hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A L hA hL ha (Localization.AtPrime m) f
      _ (pullback.fst A.hom f) (pullback.snd A.hom f) (IsPullback.of_hasPullback _ _)).1
  have hL' : (L.pull (pullback.fst A.hom f)).IsLB := LB.isLB_pull hL _
  have hj' : IsClosedImmersion ((Over.pullback f).map j).left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) f j hj
  have hfin' : IsFinite ((Over.pullback f).obj H).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite) (IsPullback.of_hasPullback H.hom f) hfin
  exact GlobalTheory.T.lineBundleKernel_flat_of_finite_noetherian_local hLaw.globalFns (Localization.AtPrime m) ((Over.pullback f).obj A) hA' hP _ hL'
    (GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy hLaw _ _ hA' hP _ hL') ((Over.pullback f).obj H)
    ((Over.pullback f).map j) hj' (GlobalTheory.T.memKernelOfLineBundle_baseChange_representable _ _ f A L hL H j hH) hfin'

end GlobalTheory.KernelFlat
