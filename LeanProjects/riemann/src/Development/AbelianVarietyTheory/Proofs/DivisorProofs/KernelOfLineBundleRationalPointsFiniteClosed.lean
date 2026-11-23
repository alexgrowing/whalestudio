import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointPrimitiveBundleEqTranslatePpav
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGenThetaOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.VeryAmpleByOfRelAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KernelFiniteFlatHolds
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KLFinite

theorem finite_of_isFinite {K : Type} [Field K] {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of K)) [IsFinite f] :
    Finite Z := by
  have : IsAffine Z := isAffine_of_isAffineHom f
  letI : Algebra K Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  have hmod : Module.Finite K Γ(Z, ⊤) := by
    show ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.Finite
    rw [CommRingCat.hom_comp]
    exact f.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  have : IsArtinianRing Γ(Z, ⊤) := IsArtinianRing.of_finite K _
  have : Finite (Spec (.of Γ(Z, ⊤))) := inferInstanceAs (Finite (PrimeSpectrum _))
  exact Finite.of_injective _ Z.isoSpec.hom.isOpenEmbedding.injective

theorem memKL_of_lam_eq_zero {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [GrpObj A] {L : LB A.left}
    (hL : L.IsLB) (x : 𝟙_ _ ⟶ A) (h : lam (cls L hL) (toUnit A ≫ x) (𝟙 A) = 0) : MemKL A L x := by
  intro p
  refine ⟨⊤, trivial, ?_⟩
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  refine (cls_eq_zero_iff (pull_isLB hD _)).1 ?_
  rw [cls_pull hD]
  refine (congrArg _ ?_).trans (map_zero _)
  have e := congrArg (CechPic.pull (snd (𝟙_ _) A).left) h
  rw [pull_lam, map_zero, Category.comp_id, ← Category.assoc, comp_toUnit, GlobalTheory.PrimitiveOverField.lam_const,
    toUnit_unique (toUnit _) (fst (𝟙_ _) A)] at e
  refine (cls_linComb hL _ _ hD).trans (Eq.trans ?_ e)
  rw [Fin.sum_univ_two, sub_eq_add_neg]
  exact congrArg₂ (· + ·) (one_zsmul _) (neg_one_zsmul _)

theorem isClosed_point {K : Type} [Field K] {A : Over (Spec (CommRingCat.of K))} [IsSeparated A.hom]
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A) : IsClosed ({x.left (IsLocalRing.closedPoint K)} : Set A.left) := by
  have hx : x.left ≫ A.hom = 𝟙 _ := Over.w x
  have : IsClosedImmersion (x.left ≫ A.hom) := by rw [hx]; infer_instance
  have : IsClosedImmersion x.left := IsClosedImmersion.of_comp x.left A.hom
  have h := x.left.isClosedEmbedding.isClosedMap {IsLocalRing.closedPoint K}
    (by rw [show ({IsLocalRing.closedPoint K} : Set (Spec (CommRingCat.of K))) = Set.univ from
      Set.eq_univ_of_forall fun z => Subsingleton.elim (α := PrimeSpectrum K) _ _]; exact isClosed_univ)
  exact (congrArg IsClosed Set.image_singleton).mp h

end GlobalTheory.KLFinite

theorem GlobalTheory.KLFinite.kl_finite : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB), Out.RelAmple A L → ∃ S : Finset A.left, (∀ s ∈ S, IsClosed ({s} : Set A.left)) ∧ ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A, GlobalTheory.CechPic.lam (cls L hL) (toUnit A ≫ x) (𝟙 A) = 0 → x.left (IsLocalRing.closedPoint K) ∈ S := by
  intro K _ _ A _ hA L hL ha
  obtain ⟨Z, i, -, hfin, -, hZ⟩ := GlobalTheory.kernelFiniteFlat_holds K A hA L hL ha
  have : Finite Z.left := GlobalTheory.KLFinite.finite_of_isFinite Z.hom
  have : IsProper A.hom := hA.proper
  have hr : (Set.range i.left).Finite := Set.finite_range _
  classical
  refine ⟨hr.toFinset.filter (fun s => IsClosed ({s} : Set A.left)), fun s hs => (Finset.mem_filter.1 hs).2,
    fun x hx => ?_⟩
  obtain ⟨z, hz⟩ := (hZ _ x).1 (GlobalTheory.KLFinite.memKL_of_lam_eq_zero hL x hx)
  refine Finset.mem_filter.2 ⟨hr.mem_toFinset.2 ⟨z.left (IsLocalRing.closedPoint K), ?_⟩,
    GlobalTheory.KLFinite.isClosed_point x⟩
  rw [← hz, Over.comp_left]
  rfl
