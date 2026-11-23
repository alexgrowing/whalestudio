import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSameGenericProjectiveCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjSpaceMapOfTupleHasDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantPowEqUnitMulSymmetricFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricThetaConstantsEqThetaMapCoordsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaConstantsProjectivelyIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteNormalisationProjectiveQuasiFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegOpen

theorem isIso_stalkMap_of_isHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M M' : RatModel o Ω}
    {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' (AlgHom.id o Ω) f) :
    IsDominant f ∧ IsIso (f.stalkMap (genericPoint M'.Z)) := by
  have hid : spMap (AlgHom.id o Ω).toRingHom ≫ M.pt = M.pt :=
    (congrArg (· ≫ M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  have : IsDominant (M'.pt ≫ f) := by
    rw [hf, hid]; infer_instance
  have hd : IsDominant f := IsDominant.of_comp M'.pt f
  refine ⟨hd, ?_⟩
  have hz : f (genericPoint M'.Z) = genericPoint M.Z := GlobalTheory.apply_genericPoint_of_isDominant f
  have key : ∀ a, M'.stalkHom (genericPoint M'.Z) (f.stalkMap (genericPoint M'.Z) a) =
      M.stalkHom (f (genericPoint M'.Z)) a := by
    intro a
    obtain ⟨U, hzU, s, rfl⟩ := M.Z.presheaf.germ_exist a
    rw [Scheme.Hom.germ_stalkMap_apply]
    exact (M'.stalkHom_germ (U := f ⁻¹ᵁ U) hzU _).trans ((hf.valF_app ⟨_, hzU⟩ s).trans (M.stalkHom_germ hzU s).symm)
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b h => M.stalkHom_injective _ ?_, fun b => ?_⟩
  · rw [← key, ← key, h]
  · have hx : M'.stalkHom (genericPoint M'.Z) b ∈ M.O (f (genericPoint M'.Z)) := by
      rw [hz, M.O_genericPoint]; exact Algebra.mem_top
    obtain ⟨a, ha⟩ := (M.stalkEquiv _).surjective ⟨_, hx⟩
    refine ⟨a, M'.stalkHom_injective _ ?_⟩
    rw [key]
    exact congrArg Subtype.val ha

end GlobalTheory.SiegOpen

namespace GlobalTheory.SiegOpen

theorem level_openImmersion : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (P : PolAV F.X) (rig : LB.Gen (P.L.pull (eSec P.A))) (m N : ℕ) (f : F.X ⟶ PSpace (cycAway n) N), ThAt F W P rig m f → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → QFin f → ∀ (Y X : RatModel o Ω) (q : Y.Z ⟶ F.X), LevAt F β u Y q → X.IsNm S.th → Geo.Tor.IsNormalScheme X.Z → ∃ d : Y.Z ⟶ X.Z, X.IsHom Y (AlgHom.id o Ω) d ∧ IsOpenImmersion d := by
  intro g n hg hn hodd F W hW P rig m N f hTh o Ω _ _ _ _ β S ρ u hSys hQ Y X q hLev hNm hXn

  have hYdiv : Y.HasDiv S.th := GlobalTheory.T.siegelThetaConstants_projectively_integral g n hg hn hodd F W hW P rig m N f hTh o Ω β S ρ u hSys Y (q ≫ f)
    hLev.1 (by rw [← Category.assoc, hLev.2.2.2.2, Category.assoc])

  obtain ⟨d, hd⟩ := hNm.exists_isHom (M' := Y) (φ := AlgHom.id o Ω) hYdiv (RatModel.isIntegrallyClosed_O hLev.1)
  refine ⟨d, hd, ?_⟩
  have hid : spMap (AlgHom.id o Ω).toRingHom ≫ X.pt = X.pt :=
    (congrArg (· ≫ X.pt) (Spec.map_id _)).trans (Category.id_comp _)
  have hYd : Y.pt ≫ d = X.pt := hd.trans hid

  obtain ⟨e, hSymE, hPe⟩ := GlobalTheory.T.exists_symmetric_theta_constants_eq_thetaMap_coords g n hg hn hodd F W hW P rig m N f hTh o Ω β S ρ u hSys
  have hSame := GlobalTheory.T.thetaConstant_pow_eq_unit_mul_symmetricFunction g n hg hn hodd F W hW P rig m N f hTh o Ω β S ρ u hSys X e hXn hNm.1 hSymE
  have hXe : X.HasDiv e := fun z => by
    obtain ⟨i, hi⟩ := hNm.1 z
    obtain ⟨j, hj, -⟩ := hSame z i hi
    exact ⟨j, hj⟩
  obtain ⟨hX, hXs, hXP⟩ := GlobalTheory.T.exists_projSpace_map_of_tuple_hasDivisor o Ω (cycAway n) β X N e hXe
  have hfs : f ≫ PSpace.str (cycAway n) N = F.s := hTh.2.2.2.2.2.2.2.1

  have heq : d ≫ hX = q ≫ f := by
    refine GlobalTheory.T.eq_of_same_generic_projective_coords (cycAway n) N Y.Z (Y.s ≫ spMap β) (d ≫ hX) (q ≫ f) Ω Y.pt e ?_ ?_ Y.gen ?_ ?_
    · rw [Category.assoc, hXs, ← Category.assoc, hd.inducedModelMorphism_comp_structureMap]
    · rw [Category.assoc, hfs, hLev.2.2.2.1]
    · rw [← Category.assoc, hYd]; exact hXP
    · rw [← Category.assoc, hLev.2.2.2.2]; exact hPe _ rfl

  have : LocallyOfFiniteType F.s := by
    haveI := F.smooth
    haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
    infer_instance
  have : LocallyOfFiniteType (f ≫ PSpace.str (cycAway n) N) := by rw [hfs]; assumption
  haveI : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (PSpace.str (cycAway n) N)
  haveI : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f (GlobalTheory.SiegMin.finite_preimage_singleton_of_qFin f hQ)
  haveI : IsFinite q := hLev.2.1
  haveI : LocallyQuasiFinite (d ≫ hX) := by rw [heq]; infer_instance
  haveI : LocallyQuasiFinite d := LocallyQuasiFinite.of_comp d hX

  haveI := Y.sep
  haveI := Y.qc
  haveI := Y.lft
  haveI := X.sep
  haveI : IsSeparated (d ≫ X.s) := by rw [hd.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : QuasiCompact (d ≫ X.s) := by rw [hd.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : LocallyOfFiniteType (d ≫ X.s) := by rw [hd.inducedModelMorphism_comp_structureMap]; infer_instance
  haveI : IsSeparated d := IsSeparated.of_comp d X.s
  haveI : QuasiCompact d := QuasiCompact.of_comp d X.s
  haveI : LocallyOfFiniteType d := locallyOfFiniteType_of_comp d X.s
  obtain ⟨h1, h2⟩ := isIso_stalkMap_of_isHom hd

  exact GlobalTheory.isOpenImmersion_of_quasiFinite_of_isIso_stalkMap d fun z => (hXn z).2

end GlobalTheory.SiegOpen
