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
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InKIffTrivialTwist
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfQuasiAffine
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVRStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.KTrivSpread

theorem kTriv_of_finite_flat {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {A : Over (Sp V)} [GrpObj A] (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) {Z : Over (Sp V)} (i : Z ⟶ A)
    [IsFinite Z.hom] [Flat Z.hom]
    (hZ : ∀ (T : Over (Sp V)) (x : T ⟶ A), MemKL A L x ↔ ∃ z : T ⟶ Z, z ≫ i = x)
    {A' : Over (Sp K)} [GrpObj A'] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap (algebraMap V K)) φ)
    {L' : LB A'.left} (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hk : KTriv A' L') : KTriv A L := by
  have := hA.proper
  have := schemeTheoreticallyDominant_fractionField V K
  let Y := pullback Z.hom (spMap (algebraMap V K))
  have : IsAffine Y := isAffine_of_isAffineHom (pullback.snd Z.hom (spMap (algebraMap V K)))
  have : IsSchemeTheoreticallyDominant (pullback.fst Z.hom (spMap (algebraMap V K))) :=
    .of_isPullback (IsPullback.of_hasPullback Z.hom (spMap (algebraMap V K))).flip
  let d : Sp Γ(Y, ⊤) ⟶ Z.left := Y.isoSpec.inv ≫ pullback.fst Z.hom (spMap (algebraMap V K))
  let t : Sp Γ(Y, ⊤) ⟶ Sp K := Y.isoSpec.inv ≫ pullback.snd Z.hom (spMap (algebraMap V K))
  have hd : d ≫ Z.hom = t ≫ spMap (algebraMap V K) := by
    simp only [d, t, Category.assoc, pullback.condition]
  have hdi : (d ≫ i.left) ≫ A.hom = t ≫ spMap (algebraMap V K) := by
    rw [Category.assoc, Over.w i, hd]
  let x : Over.mk t ⟶ A' := Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
  let z : Over.mk (t ≫ spMap (algebraMap V K)) ⟶ Z := Over.homMk d hd
  have hz : z ≫ i = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
  have hx : x = 1 := hk _ t x (memKL_of_push h hL hL' hw x ((hZ _ _).2 ⟨z, hz⟩))
  have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
  have hi : i = toUnit Z ≫ η[A] := by
    have : IsSchemeTheoreticallyDominant d := by
      dsimp only [d]; infer_instance
    refine over_ext_of_schemeTheoreticallyDominant d (congrArg (fun q => q.left)
      (show z ≫ i = z ≫ toUnit Z ≫ η[A] from ?_))
    rw [hz, hx', ← Category.assoc, comp_toUnit]
    rfl
  intro R _ s y hy
  obtain ⟨u, rfl⟩ := (hZ _ y).1 hy
  rw [hi, ← Category.assoc, comp_toUnit]

theorem kTriv_of_generic_fibre : Laws → ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (P : PolAV (Sp K)) (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B] (M : GlobalTheory.UU.CP B) (φ : P.A.left ⟶ B.left), IsAbelianScheme B → IsGrpPullback P.A B (spMap (algebraMap V K)) φ → LBIso P.L (M.L.L.pull φ) → RelAmple B M.L.L → KTriv B M.L.L := by
  intro hL V K _ _ _ _ _ _ P B _ _ M φ hB h hw ha
  have hM := M.L.isLB
  have hP : AbLaw.IsProjBy B.hom :=
    (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B M.L.L hB hM ha V (𝟙 _) B.left (𝟙 _) B.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  obtain ⟨hO, hu, hK⟩ := UU.TrivTwist.inK_iff_trivial_twist _ B M.L.L hM
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hL.globalFns V B hB hP M.L.L _ hM hO
  have hfin : IsFinite H.hom :=
    AmpleStabFinite.isFinite_of_relAmple hL.globalFns V B hB M.L.L _ hM hO ha H j hj hH
  have hflat : Flat H.hom := GlobalTheory.T.flat_kernelPolarisation_cosets_over_DVR hL.globalFns V B hB hP M.L M.c _ hO hu H j hj hH hfin
  exact kTriv_of_finite_flat hB hM j (fun T x => (hK _ rfl T x).trans (hH T x)) h P.isLB hw P.ktriv

end GlobalTheory.KTrivSpread
end
