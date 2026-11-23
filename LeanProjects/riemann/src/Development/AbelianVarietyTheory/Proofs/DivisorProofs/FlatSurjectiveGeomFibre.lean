import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowFlatLocallyQuasiFinite
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FlatAndSurjectiveOfSurjectivePoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RingHomFlatCodescendsAlongFaithfullyFlat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory.Limits
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.IsogenyQuasiInverse

theorem isIntegral_left {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left := by
  have := hA.smooth
  have := hA.geomConnected
  exact isIntegral_of_smooth_of_geometricallyConnected A.hom

theorem nonempty_left {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] : Nonempty A.left :=
  ⟨η[A].left (IsLocalRing.closedPoint K)⟩

theorem krullDim_eq {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ)
    (hAg : SmoothOfRelativeDimension g A.hom) : Order.krullDim A.left = g := by
  have := nonempty_left A
  rw [← PosBaseChange.dim_eq_krullDim]
  exact HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth A.hom g hAg

theorem apply_genericPoint {K : Type} [Field K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g : ℕ)
    [IsIntegral A.left] [IsIntegral B.left] (hAg : SmoothOfRelativeDimension g A.hom)
    (hBg : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [LocallyQuasiFinite f.left] :
    f.left (genericPoint A.left) = genericPoint B.left := by
  have hdA := krullDim_eq A g hAg
  have hdB := krullDim_eq B g hBg
  have hs := FiniteEndFlat.strictMono_of_locallyQuasiFinite f.left
  have h1 : (g : WithBot ℕ∞) ≤ Order.height (genericPoint A.left) := by
    rw [← hdA, Order.krullDim_eq_iSup_height]
    exact iSup_le fun a => WithBot.coe_le_coe.mpr (Order.height_mono (genericPoint_specializes a))
  have h2 := Order.height_le_height_apply_of_strictMono _ hs (genericPoint A.left)
  have h3 : (Order.height (genericPoint B.left) : WithBot ℕ∞) ≤ g := by
    rw [← hdB]; exact Order.height_le_krullDim _
  by_contra hne
  have hle : f.left (genericPoint A.left) ≤ genericPoint B.left := genericPoint_specializes _
  have hlt : f.left (genericPoint A.left) < genericPoint B.left :=
    lt_of_le_not_ge hle fun h => hne (Specializes.antisymm (show f.left (genericPoint A.left) ⤳ genericPoint B.left from h) hle).eq
  have hfin : Order.height (f.left (genericPoint A.left)) < ⊤ := by
    exact lt_of_le_of_lt (Order.height_mono hlt.le) (lt_of_le_of_lt (WithBot.coe_le_coe.mp h3) (ENat.coe_lt_top g))
  have h4 := Order.height_strictMono hlt hfin
  have : (g : WithBot ℕ∞) < g := calc
    (g : WithBot ℕ∞) ≤ Order.height (genericPoint A.left) := h1
    _ ≤ Order.height (f.left (genericPoint A.left)) := WithBot.coe_le_coe.mpr h2
    _ < Order.height (genericPoint B.left) := WithBot.coe_lt_coe.mpr h4
    _ ≤ g := h3
  exact lt_irrefl _ this

end GlobalTheory.IsogenyQuasiInverse

namespace GlobalTheory.IsogenyQuasiInverse

theorem pullback_data {S T : Scheme.{0}} (s : T ⟶ S) (A : Over S) [GrpObj A] (g : ℕ)
    (hA : IsAbelianScheme A) (hAg : SmoothOfRelativeDimension g A.hom) :
    IsAbelianScheme ((Over.pullback s).obj A) ∧
      SmoothOfRelativeDimension g ((Over.pullback s).obj A).hom :=
  ⟨isAbelianScheme_pullback_obj s A hA,
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.hom s) hAg⟩

theorem flat_surjective_of_field {K : Type} [Field K] [IsAlgClosed K] (A B : Over (Sp K))
    [GrpObj A] [GrpObj B] (g : ℕ) (hA : IsAbelianScheme A) (hB : IsAbelianScheme B)
    (hAg : SmoothOfRelativeDimension g A.hom) (hBg : SmoothOfRelativeDimension g B.hom)
    (f : A ⟶ B) [IsMonHom f] [LocallyQuasiFinite f.left] : Flat f.left ∧ Surjective f.left := by
  have := isIntegral_left A hA
  have := isIntegral_left B hB
  have := hA.proper
  have := hB.proper
  have := hA.smooth
  have := hB.smooth
  have : IsProper (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper f.left := IsProper.of_comp _ B.hom
  have hξ := apply_genericPoint A B g hAg hBg f
  have hd : DenseRange f.left := by
    rw [DenseRange, dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro y
    exact ((genericPoint_specializes y).mem_closed isClosed_closure (subset_closure ⟨_, hξ⟩))
  have : IsDominant f.left := ⟨hd⟩
  refine ⟨SS.flat_of_isDominant_grpHom K A B f, ⟨fun y => ?_⟩⟩
  have hc : IsClosed (Set.range f.left) := f.left.isClosedMap.isClosed_range
  exact (genericPoint_specializes y).mem_closed hc ⟨_, hξ⟩

end GlobalTheory.IsogenyQuasiInverse

namespace GlobalTheory.IsogenyQuasiInverse

theorem flat_surjective_geomFibre {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (g : ℕ)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hAg : SmoothOfRelativeDimension g A.hom)
    (hBg : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [IsMonHom f] [LocallyQuasiFinite f.left]
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ S) :
    Flat ((Over.pullback t).map f).left ∧ Surjective ((Over.pullback t).map f).left := by
  obtain ⟨hA', hAg'⟩ := pullback_data t A g hA hAg
  obtain ⟨hB', hBg'⟩ := pullback_data t B g hB hBg
  have : LocallyQuasiFinite ((Over.pullback t).map f).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (AbLaw.MulN.isPullback_baseChange t f)
      inferInstance
  exact flat_surjective_of_field _ _ g hA' hB' hAg' hBg' _

theorem flat_fibre {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] (g : ℕ)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hAg : SmoothOfRelativeDimension g A.hom)
    (hBg : SmoothOfRelativeDimension g B.hom) (f : A ⟶ B) [IsMonHom f] [LocallyQuasiFinite f.left]
    (k : Type) [Field k] (s : Sp k ⟶ S) : Flat ((Over.pullback s).map f).left := by
  refine flat_of_flat_fieldBaseChange k (AlgebraicClosure k) (algebraMap _ _) _ _ _ ?_
  obtain ⟨hA', hAg'⟩ := pullback_data s A g hA hAg
  obtain ⟨hB', hBg'⟩ := pullback_data s B g hB hBg
  have : LocallyQuasiFinite ((Over.pullback s).map f).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (AbLaw.MulN.isPullback_baseChange s f)
      inferInstance
  exact (flat_surjective_geomFibre _ _ g hA' hB' hAg' hBg' _ _ _).1

end GlobalTheory.IsogenyQuasiInverse

namespace GlobalTheory.IsogenyQuasiInverse

theorem exists_quasiInverse : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A B : Over (Sp R))
    [GrpObj A] [GrpObj B] (g : ℕ),
    IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
    SmoothOfRelativeDimension g B.hom → ∀ f : A ⟶ B, IsMonHom f → ∀ m : ℕ, 0 < m →
    (∀ (T : Over (Sp R)) (x : T ⟶ A), x ≫ f = 1 → x ^ m = 1) →
    ∃ h : B ⟶ A, IsMonHom h ∧ f ≫ h = 𝟙 A ^ m ∧ h ≫ f = 𝟙 B ^ m := by
  intro R _ _ A B _ _ g hA hB hAg hBg f hf m hm hker
  have := hA.smooth
  have := hB.smooth
  have := hA.proper
  have := hB.proper
  have := hA.comm
  have : LocallyOfFiniteType (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (f.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact f.left := QuasiCompact.of_comp _ B.hom
  have hSA := isSemiAbelian_of_isAbelianScheme A hA
  have : LocallyQuasiFinite f.left :=
    locallyQuasiFinite_of_finite_geometric_ker _ A B f hf inferInstance inferInstance
      fun Ω _ _ t => by
        have := HomExt.finite_torsion_points hSA t hm
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ m = 1})
          (fun x => ⟨x.1, hker _ x.1 x.2⟩) fun a b e => Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ m = 1} => z.1) e)
  have hflat : Flat f.left :=
    SemiAbMulFlat.flat_of_flatOver_fields f.left B.hom inferInstance
      (by rw [Over.w]; infer_instance) (by rw [Over.w]; infer_instance) inferInstance
      fun k _ s => FibreFlat.flatOver_of_pullback f s (flat_fibre A B g hA hB hAg hBg f k s)
  have hsurj : Surjective f.left :=
    AbLaw.MulN.surjective_of_geomFibres f fun K _ _ t =>
      (flat_surjective_geomFibre A B g hA hB hAg hBg f K t).2
  have hmA : IsMonHom (𝟙 A ^ m) := AbLaw.MulN.isMonHom_mulA A m
  obtain ⟨⟨h, hh, hfh⟩, hepi⟩ := exists_monHom_factor_of_flat_surjective _ A B A f (𝟙 A ^ m) hf hmA
    hflat hsurj inferInstance fun T x hx => by
      rw [MonObj.comp_pow, Category.comp_id, hker T x hx]
  refine ⟨h, hh, hfh, ?_⟩
  rw [← cancel_epi f, ← Category.assoc, hfh, MonObj.pow_comp, Category.id_comp, MonObj.comp_pow,
    Category.comp_id]

end GlobalTheory.IsogenyQuasiInverse
