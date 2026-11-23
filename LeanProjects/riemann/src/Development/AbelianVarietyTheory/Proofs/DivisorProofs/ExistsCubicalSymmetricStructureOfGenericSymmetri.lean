import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCubicalRigidifiedExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMaps
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSymmetricIffExistsGen
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.H0IsIffNonemptyLinearEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStrOfTrivTheta
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetryCubicalBundleOfDenseAbelianNormalBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CubSymPkg

theorem exists_cp_of_generic_sym : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → IsProper (pullback.snd G.hom (jK R)) → ∀ L : LB G.left, L.IsLB → Out.Sym ((Over.pullback (jK R)).obj G) (L.pull (pullback.fst G.hom (jK R))) → ∃ P : GlobalTheory.UU.CP G, P.L.L = L := by
  intro R _ _ _ _ _ G _ _ hG hP L hL hS
  have laws : Out.Laws := GlobalTheory.lawsAndExpansions.1.1
  have := hG.smooth
  have := hG.geomConnected
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have : QuasiCompact (jK R) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have hN : Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.ZJ.isNormalScheme_sp R
  let A := (Over.pullback (jK R)).obj G
  let F : A.left ⟶ G.left := pullback.fst G.hom (jK R)
  have gp : IsGrpPullback A G (jK R) F := isGrpPullback_pullback G (jK R)
  have hsA : IsSemiAbelian A := Geo.Tor.IsSemiAbelian.pullback (jK R) G hG
  have : IsProper A.hom := hP
  have hA : IsAbelianScheme A := Geo.Tor.AbelianSchemeGerms.isAbelianScheme_of_proper A hsA
  have hM : (L.pull F).IsLB := pull_isLB hL F

  obtain ⟨rA, hrA⟩ := DVR.exists_gen_of_isLB_local _ (pull_isLB hM (eSec A))
  let LA : RigLB A := ⟨L.pull F, rA, hM, hrA⟩
  obtain ⟨t, ht⟩ := GlobalTheory.GenericAmpleDvr.triv_theta hA hM
  obtain ⟨t', ht', hn⟩ := AbLaw.Cube.exists_normalised hM t ht
  let cA : CubicalStr A LA := AbLaw.Cube.cubicalOfNormalised laws.globalFns hA LA t' ht' hn
  obtain ⟨s₀, hs₀⟩ := (GlobalTheory.ZV.symB_iff_exists_gen _).1 ((GlobalTheory.ZV.symB_iff_sym hM).2 hS)
  obtain ⟨s₁, hs₁, hr₁⟩ := GlobalTheory.AbPackage.exists_rigidified_sym hM s₀ hs₀
  have symA : LA.IsSymmetric := (GlobalTheory.isSymmetric_iff_exists_gen _ A LA).2 ⟨s₁, hs₁, hr₁⟩

  obtain ⟨r, hr⟩ := DVR.exists_gen_of_isLB_local _ (pull_isLB hL (eSec G))
  let L' : RigLB G := ⟨L, r, hL, hr⟩
  have hw : PGen (GlobalTheory.UU.pullIso L F) := (isGen_iff _).1 (GlobalTheory.UU.pullIso_isGen hL F)
  obtain ⟨c', -⟩ := GlobalTheory.DenseCubeExt.exists_cubical (L := LA) hN gp cA L' hw
  obtain ⟨s, hs, hrs⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ G L').1
    (GlobalTheory.DenseCubeExt.isSymmetric (L := LA) hN gp L' hw symA)
  exact ⟨⟨L', c', s, hs, hrs, GlobalTheory.T.symmetry_cubicalBundle_of_dense_abelian_normal_base hN (jK R) G A F gp laws.globalFns hA L' c' s hs hrs⟩, rfl⟩

end GlobalTheory.CubSymPkg
