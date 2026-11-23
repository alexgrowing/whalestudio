import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.Published

def SemiAbelianHomExtension : Prop :=
  ∀ (S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S →
    ∀ (U : S.Opens), Dense (U : Set S) →
    ∀ (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H →
    ∀ f : (Over.pullback U.ι).obj G ⟶ (Over.pullback U.ι).obj H, IsMonHom f →
      ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback U.ι).map F = f

namespace SemiAbelianHomExtension

open ExtUnique

variable {S U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S]

theorem quasiCompact_and_dominant (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (j : U ⟶ S) [IsOpenImmersion j]
    [IsDominant j] : QuasiCompact j ∧ IsSchemeTheoreticallyDominant j :=
  have := GlobalTheory.IsNormalScheme.of_pred hS
  dense_openImmersion j

theorem of_isGrpPullback (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    {j : U ⟶ S} [IsOpenImmersion j] [IsDominant j] {G H : Over S} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over U} [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback H' H j ψ)
    (f : G' ⟶ H') [IsMonHom f] : ∃! F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, -⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨-, _⟩ := flat_and_isSeparated_of_isSemiAbelian H hH
  let V : S.Opens := j.opensRange
  have hV : Dense (V : Set S) := j.denseRange
  let e : V.toScheme ⟶ U := j.isoOpensRange.inv
  have he : e ≫ j = V.ι := j.isoOpensRange_inv_comp
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G V.ι)
    (((isGrpPullback_pullback G' e).comp hφ).congr he rfl)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso (((isGrpPullback_pullback H' e).comp hψ).congr he rfl)
    (isGrpPullback_pullback H V.ι)
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := h S hS V hV G H hG hH (a.hom ≫ (Over.pullback e).map f ≫ b.hom) inferInstance
  have key : f.left ≫ ψ = φ ≫ F.left := by
    have h₁ := pullback_map_left_fst V.ι F
    rw [hF', Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← ha', Category.assoc,
      ← Category.assoc ((Over.pullback e).map f).left, pullback_map_left_fst, Category.assoc,
      Category.assoc] at h₁
    have : IsIso a.hom.left := inferInstanceAs (IsIso ((Over.forget _).map a.hom))
    exact (cancel_epi (pullback.fst G'.hom e)).1 ((cancel_epi a.hom.left).1 h₁)
  exact ⟨F, ⟨hF, key⟩, fun F' hF' => over_hom_ext_of_isPullback hφ.1 (hF'.2.symm.trans key)⟩

theorem of_isOpenImmersion (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (j : U ⟶ S) [IsOpenImmersion j] [IsDominant j] {G H : Over S} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H)
    [IsMonHom f] : ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback j).map F = f := by
  obtain ⟨F, ⟨hF, hF'⟩, hu⟩ := h.of_isGrpPullback hS hG hH (isGrpPullback_pullback G j)
    (isGrpPullback_pullback H j) f
  refine ⟨F, ⟨hF, ?_⟩, fun F' hF' => hu F' ⟨hF'.1, ?_⟩⟩
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · exact (pullback_map_left_fst j F).trans hF'.symm
    · exact (Over.w _).trans (Over.w _).symm
  · rw [← hF'.2]
    exact pullback_map_left_fst j F'

theorem mapGrp_map_bijective (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (j : U ⟶ S) [IsOpenImmersion j] [IsDominant j] (G H : Grp (Over S))
    (hG : IsSemiAbelian G.X) (hH : IsSemiAbelian H.X) :
    Function.Bijective ((Over.pullback j).mapGrp.map : (G ⟶ H) → _) := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, -⟩ := flat_and_isSeparated_of_isSemiAbelian G.X hG
  obtain ⟨-, _⟩ := flat_and_isSeparated_of_isSemiAbelian H.X hH
  refine ⟨mapGrp_map_injective j G H, fun f => ?_⟩
  have : IsMonHom (M := (Over.pullback j).obj G.X) (N := (Over.pullback j).obj H.X) f.hom.hom :=
    f.hom.isMonHom_hom
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := h.of_isOpenImmersion hS j hG hH f.hom.hom
  refine ⟨Grp.homMk F, ?_⟩
  ext1
  exact hF'

theorem existsUnique_oAct_of_isGrpPullback (h : SemiAbelianHomExtension)
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) {j : U ⟶ S} [IsOpenImmersion j] [IsDominant j]
    {G : Over S} [GrpObj G] (hG : IsSemiAbelian G) {G' : Over U} [GrpObj G'] {φ : G'.left ⟶ G.left}
    (hφ : IsGrpPullback G' G j φ) {O : Type} [CommRing O] (i : OAct O G') :
    ∃! a : OAct O G, ∀ x, (i.act x).left ≫ φ = φ ≫ (a.act x).left := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  refine ExtUnique.existsUnique_oAct_of_isGrpPullback hφ i fun x => ?_
  have := i.hom x
  obtain ⟨F, ⟨-, hF⟩, -⟩ := h.of_isGrpPullback hS hG hG hφ hφ (i.act x)
  exact ⟨F, hF⟩

theorem existsUnique_oAct (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (j : U ⟶ S) [IsOpenImmersion j] [IsDominant j] {G : Over S} [GrpObj G] [IsCommMonObj G]
    (hG : IsSemiAbelian G) {O : Type} [CommRing O] (i : OAct O ((Over.pullback j).obj G)) :
    ∃! a : OAct O G, OAct.pullback j G a = i := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  refine existsUnique_oAct_pullback j i fun x => ?_
  have := i.hom x
  obtain ⟨F, ⟨-, hF⟩, -⟩ := h.of_isOpenImmersion hS j hG hG (i.act x)
  exact ⟨F, hF⟩

theorem existsUnique_iso_of_isGrpPullback (h : SemiAbelianHomExtension)
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) {j : U ⟶ S} [IsOpenImmersion j] [IsDominant j]
    {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over U}
    [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G j φ)
    (hψ : IsGrpPullback H' H j ψ) (e : G' ≅ H') [IsMonHom e.hom] :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ e.hom.left ≫ ψ = φ ≫ E.hom.left := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨F, ⟨hF, hF'⟩, hu⟩ := h.of_isGrpPullback hS hG hH hφ hψ e.hom
  obtain ⟨F₁, ⟨-, hF₁⟩, -⟩ := h.of_isGrpPullback hS hH hG hψ hφ e.inv
  obtain ⟨h₁, h₂⟩ := comp_eq_id_of_isPullback hφ.1 hψ.1 e F F₁ hF' hF₁
  exact ⟨⟨F, F₁, h₁, h₂⟩, ⟨hF, hF'⟩, fun E hE => Iso.ext (hu E.hom hE)⟩

theorem existsUnique_iso (h : SemiAbelianHomExtension) (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (j : U ⟶ S) [IsOpenImmersion j] [IsDominant j] {G H : Over S} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) (e : (Over.pullback j).obj G ≅ (Over.pullback j).obj H)
    [IsMonHom e.hom] : ∃! E : G ≅ H, IsMonHom E.hom ∧ (Over.pullback j).map E.hom = e.hom := by
  obtain ⟨_, _⟩ := quasiCompact_and_dominant hS j
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨F, ⟨hF, hF'⟩, hu⟩ := h.of_isOpenImmersion hS j hG hH e.hom
  obtain ⟨F₁, ⟨-, hF₁⟩, -⟩ := h.of_isOpenImmersion hS j hH hG e.inv
  obtain ⟨h₁, h₂⟩ := comp_eq_id_of_pullback j e F F₁ hF' hF₁
  exact ⟨⟨F, F₁, h₁, h₂⟩, ⟨hF, hF'⟩, fun E hE => Iso.ext (hu E.hom hE)⟩

theorem existsUnique_iso_of_extensions (h : SemiAbelianHomExtension)
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) {j : U ⟶ S} [IsOpenImmersion j] [IsDominant j]
    {A : Over U} [GrpObj A] {G H : Over S} [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    {φ : A.left ⟶ G.left} {ψ : A.left ⟶ H.left} (hφ : IsGrpPullback A G j φ) (hψ : IsGrpPullback A H j ψ) :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ φ ≫ E.hom.left = ψ := by
  have : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  simpa [eq_comm] using h.existsUnique_iso_of_isGrpPullback hS hG hH hφ hψ (Iso.refl A)

omit [AlgebraicGeometry.IsNoetherian S] in

theorem act_comp_of_isPullback {j : U ⟶ S} [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    {G H : Over S} [GrpObj G] [GrpObj H] [Flat G.hom] [IsSeparated H.hom] {G' H' : Over U} [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsPullback φ G'.hom G.hom j)
    {O : Type} [CommRing O] (a : OAct O G) (b : OAct O H) (a' : OAct O G') (b' : OAct O H')
    (ha : ∀ x, (a'.act x).left ≫ φ = φ ≫ (a.act x).left) (hb : ∀ x, (b'.act x).left ≫ ψ = ψ ≫ (b.act x).left)
    (f : G' ⟶ H') (hf : ∀ x, a'.act x ≫ f = f ≫ b'.act x) (F : G ⟶ H) (hF : f.left ≫ ψ = φ ≫ F.left) (x : O) :
    a.act x ≫ F = F ≫ b.act x := by
  refine over_hom_ext_of_isPullback hφ ?_
  rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← ha, Category.assoc, ← hF, ← Category.assoc,
    ← Over.comp_left, hf, Over.comp_left, Category.assoc, hb, ← Category.assoc, hF, Category.assoc]

section Dvr

variable (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
  [IsFractionRing T K]

theorem isOpenImmersion_generic_dvr : IsOpenImmersion (spMap (algebraMap T K)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have : IsLocalization.Away ϖ K := by
    refine (isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} hxy => ⟨1, by
      rw [IsFractionRing.injective T K hxy]⟩⟩
    · rintro ⟨_, n, rfl⟩
      exact IsUnit.mk0 _ (by simp [hϖ.ne_zero])
    · obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors T) z
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hϖ
      refine ⟨⟨a * (u⁻¹ : Tˣ), ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
      have hab' : z * algebraMap T K (u * ϖ ^ n) = algebraMap T K a := hu ▸ hab
      change z * algebraMap T K (ϖ ^ n) = algebraMap T K (a * (u⁻¹ : Tˣ))
      rw [map_mul, ← hab', _root_.mul_assoc, ← map_mul, mul_right_comm, Units.mul_inv, _root_.one_mul]
  exact IsOpenImmersion.of_isLocalization ϖ

theorem isDominant_generic_dvr : IsDominant (spMap (algebraMap T K)) :=
  have := (spec_fractionRing T K).1
  have := (spec_fractionRing T K).2
  inferInstance

theorem isNormalScheme_dvr : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp T) :=
  GlobalTheory.IsNormalScheme.pred _

variable {T K}

theorem dvr (h : SemiAbelianHomExtension) {G H : Over (Sp T)} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj H)
    [IsMonHom f] : ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f :=
  have := isOpenImmersion_generic_dvr T K
  have := isDominant_generic_dvr T K
  h.of_isOpenImmersion (isNormalScheme_dvr T) _ hG hH f

theorem dvr_of_isGrpPullback (h : SemiAbelianHomExtension) {G H : Over (Sp T)} [GrpObj G] [GrpObj H]
    (hG : IsSemiAbelian G) (hH : IsSemiAbelian H) {G' H' : Over (Sp K)} [GrpObj G'] [GrpObj H']
    {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left} (hφ : IsGrpPullback G' G (spMap (algebraMap T K)) φ)
    (hψ : IsGrpPullback H' H (spMap (algebraMap T K)) ψ) (f : G' ⟶ H') [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left :=
  have := isOpenImmersion_generic_dvr T K
  have := isDominant_generic_dvr T K
  h.of_isGrpPullback (isNormalScheme_dvr T) hG hH hφ hψ f

end Dvr

section Model

open scoped TensorProduct

theorem smooth_laurent (R : Type) [CommRing R] : Algebra.Smooth R (AddMonoidAlgebra R (ULift.{0} ℤ)) := by
  have h₁ : Algebra.Smooth (Polynomial R) (LaurentPolynomial R) :=
    Algebra.Smooth.of_isLocalization_Away (Polynomial.X : Polynomial R)
  have h₀ : Algebra.Smooth R (Polynomial R) := ⟨inferInstance, inferInstance⟩
  have : IsScalarTower R (Polynomial R) (LaurentPolynomial R) :=
    IsScalarTower.of_algebraMap_eq fun r => (Polynomial.toLaurent_C r).symm
  have h₂ : Algebra.Smooth R (LaurentPolynomial R) := Algebra.Smooth.comp R (Polynomial R) _
  exact Algebra.Smooth.of_equiv (AddMonoidAlgebra.domCongr R R (AddEquiv.ulift (α := ℤ)).symm)

theorem smooth_splitTorusAff : Smooth (splitTorusAff ZU.{0} (ULift.{0} ℤ)).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (algebraMap ZU.{0} (AddMonoidAlgebra ZU.{0} (ULift.{0} ℤ)))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.2 (smooth_laurent _)

theorem geometricallyConnected_laurent (R : Type) [CommRing R] : GeometricallyConnected
    (Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R (ULift.{0} ℤ))))) := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ ↦ ?_⟩
  have : IsDomain (AddMonoidAlgebra K (ULift.{0} ℤ)) :=
    (AddMonoidAlgebra.domCongr K K (AddEquiv.ulift (α := ℤ))).toMulEquiv.isDomain _
  have : IsDomain (AddMonoidAlgebra R (ULift.{0} ℤ) ⊗[R] K) :=
    ((Algebra.TensorProduct.comm _ _ _).toRingEquiv.trans
      (AddMonoidAlgebra.scalarTensorEquiv (M := ULift.{0} ℤ) R K).toRingEquiv).toMulEquiv.isDomain _
  let e := (pullbackSpecIso R (AddMonoidAlgebra R (ULift.{0} ℤ)) K).inv
  exact e.homeomorph.surjective.connectedSpace e.homeomorph.continuous

theorem geometricallyConnected_splitTorusAff :
    GeometricallyConnected (splitTorusAff ZU.{0} (ULift.{0} ℤ)).hom :=
  geometricallyConnected_laurent (ULift.{0} ℤ)

theorem isAbelianScheme_unit (S : Scheme.{0}) : IsAbelianScheme (𝟙_ (Over S)) := by
  refine ⟨inferInstance, inferInstanceAs (Smooth (𝟙 S)), inferInstanceAs (IsProper (𝟙 S)), ?_⟩
  change GeometricallyConnected (𝟙 S)
  refine ⟨fun K _ y Z fst snd H => ?_⟩
  have : IsIso snd := H.isIso_snd_of_isIso
  exact snd.homeomorph.symm.surjective.connectedSpace snd.homeomorph.symm.continuous

theorem isSemiAbelian_Gm (S : Scheme.{0}) : IsSemiAbelian (Gm S) := by
  have h₁ := smooth_splitTorusAff
  have h₂ := geometricallyConnected_splitTorusAff
  have h₃ := (splitTorusAff_flat_and_isSeparated ZU.{0} (ULift.{0} ℤ)).2
  have h₄ : QuasiCompact (splitTorusAff ZU.{0} (ULift.{0} ℤ)).hom := by
    change QuasiCompact (Spec.map _); infer_instance
  have h₅ : IsCommMonObj (splitTorusAff ZU.{0} (ULift.{0} ℤ)) := by
    have : Coalgebra.IsCocomm ZU.{0} (torusRing ZU.{0} (ULift.{0} ℤ)) :=
      inferInstanceAs (Coalgebra.IsCocomm ZU.{0} (AddMonoidAlgebra ZU.{0} (ULift.{0} ℤ)))
    infer_instance
  have sm : ∀ S : Scheme.{0}, Smooth (Gm S).hom := fun S =>
    inferInstanceAs (Smooth (pullback.snd _ (toZ S)))
  have gc : ∀ S : Scheme.{0}, GeometricallyConnected (Gm S).hom := fun S =>
    inferInstanceAs (GeometricallyConnected (pullback.snd _ (toZ S)))
  have qc : ∀ S : Scheme.{0}, QuasiCompact (Gm S).hom := fun S =>
    inferInstanceAs (QuasiCompact (pullback.snd _ (toZ S)))
  refine ⟨inferInstanceAs (IsCommMonObj ((Over.pullback (toZ S)).obj _)), sm S,
    inferInstanceAs (IsSeparated (pullback.snd _ (toZ S))), qc S, gc S, fun Ω _ _ p => ?_⟩
  obtain ⟨e, he, -⟩ := splitTorus_baseChange S _ p (ULift.{0} ℤ)
  refine ⟨torusExtOfIso e
    { X := ULift.{0} ℤ
      B := 𝟙_ _
      isAbelian := isAbelianScheme_unit _
      q := toUnit _
      q_hom := inferInstance
      q_flat := ?_
      q_surjective := ?_
      q_quasiCompact := ?_
      i := 𝟙 _
      i_hom := inferInstance
      isKernel := ?_ }⟩
  · have := sm (Spec (.of Ω))
    exact inferInstanceAs (Flat (Gm (Spec (.of Ω))).hom)
  · have := gc (Spec (.of Ω))
    exact inferInstanceAs (Surjective (Gm (Spec (.of Ω))).hom)
  · exact qc _
  · have : IsIso (η : 𝟙_ (Over (Spec (.of Ω))) ⟶ 𝟙_ _) := by
      rw [toUnit_unique η (𝟙 _)]; infer_instance
    exact IsPullback.of_horiz_isIso ⟨toUnit_unique _ _⟩

theorem nontrivial_Gm_int : Nontrivial (𝟙_ (Over (Sp ℤ)) ⟶ Gm (Sp ℤ)) := by
  refine (splitTorusPointsEquiv (Sp ℤ) (ULift.{0} ℤ) (𝟙_ _)).toEquiv.nontrivial_congr.2 ?_
  refine ⟨(zpowersHom _ (-1)).comp (AddEquiv.toMultiplicative (AddEquiv.ulift (α := ℤ))).toMonoidHom, 1,
    fun h => ?_⟩
  have h₀ := DFunLike.congr_fun h (Multiplicative.ofAdd (ULift.up 1))
  change (-1 : Γ(Sp ℤ, ⊤)ˣ) ^ (1 : ℤ) = 1 at h₀
  rw [zpow_one] at h₀
  have h₁ : (-1 : Γ(Sp ℤ, ⊤)) = 1 := congrArg Units.val h₀
  have h₂ := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom.hom h₁
  rw [map_neg, map_one] at h₂
  exact absurd h₂ (by decide : (-1 : ℤ) ≠ 1)

theorem model_int : AlgebraicGeometry.IsNoetherian (Sp ℤ) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp ℤ) ∧
    ∃ U : (Sp ℤ).Opens, Dense (U : Set (Sp ℤ)) ∧ U ≠ ⊤ ∧ IsSemiAbelian (Gm (Sp ℤ)) ∧
      Nontrivial (𝟙_ (Over (Sp ℤ)) ⟶ Gm (Sp ℤ)) ∧
      ∀ F₀ : Gm (Sp ℤ) ⟶ Gm (Sp ℤ), IsMonHom F₀ → IsMonHom ((Over.pullback U.ι).map F₀) ∧
        ∃! F : Gm (Sp ℤ) ⟶ Gm (Sp ℤ), IsMonHom F ∧ (Over.pullback U.ι).map F = (Over.pullback U.ι).map F₀ := by
  let U : (Sp ℤ).Opens := PrimeSpectrum.basicOpen (2 : ℤ)
  have hU : Dense (U : Set (Sp ℤ)) :=
    U.isOpen.dense ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℤ), by
      change (2 : ℤ) ∉ (⊥ : Ideal ℤ)
      simp⟩
  refine ⟨inferInstance, GlobalTheory.IsNormalScheme.pred _, U, hU, fun h => ?_, isSemiAbelian_Gm _, nontrivial_Gm_int,
    fun F₀ hF₀ => ⟨inferInstance, F₀, ⟨hF₀, rfl⟩, fun F hF => ?_⟩⟩
  · have h₂ : (⟨Ideal.span {2}, (Ideal.span_singleton_prime two_ne_zero).2 Int.prime_two⟩ : PrimeSpectrum ℤ) ∈
        PrimeSpectrum.basicOpen (2 : ℤ) := by
      change _ ∈ U
      rw [h]
      trivial
    exact h₂ (Ideal.mem_span_singleton_self _)
  · obtain ⟨_, _⟩ := dense_open U hU
    obtain ⟨_, _⟩ := flat_and_isSeparated_of_isSemiAbelian _ (isSemiAbelian_Gm (Sp ℤ))
    exact pullback_map_injective U.ι _ _ hF.2

end Model

end SemiAbelianHomExtension

end GlobalTheory.Published
