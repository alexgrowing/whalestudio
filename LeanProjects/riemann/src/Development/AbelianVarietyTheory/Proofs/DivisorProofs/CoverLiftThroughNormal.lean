import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGeneric
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.NormCoverFin

theorem isDominant_j {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) : IsDominant V.j := by
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : Flat V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  refine ⟨?_⟩
  obtain ⟨x⟩ : Nonempty V.G := inferInstance
  have h0 : genericPoint V.X ∈ Set.range V.j :=
    (Flat.generalizingMap V.j).stableUnderGeneralization_range (genericPoint_specializes (V.j x)) ⟨x, rfl⟩
  have h2 : closure ({genericPoint V.X} : Set V.X) ⊆ closure (Set.range V.j) :=
    closure_mono (Set.singleton_subset_iff.2 h0)
  rw [show closure ({genericPoint V.X} : Set V.X) = Set.univ from genericPoint_spec V.X] at h2
  exact dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset h2)

theorem exists_cover : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V V₂ : Mean4O.Cover Y) (G : Scheme.{0})
    [IsIntegral G] [GlobalTheory.IsNormalScheme G] (g : G ⟶ V.G) [IsFinite g] [IsDominant g] (k : G ⟶ V₂.G),
    k ≫ V₂.π = g ≫ V.π →
    ∃ (W : Mean4O.Cover Y) (a : W.X ⟶ V.X) (k' : W.G ⟶ V₂.G), a ≫ V.p = W.p ∧ Lies W V a ∧ k' ≫ V₂.π = W.π := by
  intro F _ _ Y V V₂ G _ _ g _ _ k hk
  have := V.ar.isLocallyNoetherian
  have : IsProper V.p := CommonModel.isProper_of_isProjOver V.ar.isProjOver
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : IsAffineHom V.j := MorphismProperty.of_isPullback V.pb.flip (isAffineHom_of_isAffine _)
  have : IsDominant V.j := isDominant_j V
  let h : G ⟶ V.X := g ≫ V.j
  have hh : h = g ≫ 𝟙 _ ≫ V.j := by simp [h]
  have hpb := GlobalTheory.isPullback_toNormalization_of_isLocalization (nonZeroDivisors (𝓞 F)) V.pb g (𝟙 _) h hh
  rw [Category.id_comp] at hpb
  have w : h ≫ V.p = (g ≫ V.π ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [h, Category.assoc, V.pb.w]
  have hfin : IsFinite h.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) h V.p F (g ≫ V.π ≫ Y.str) w
  have : GlobalTheory.IsNormalScheme h.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral h
  have hint : IsIntegral h.normalization := inferInstance
  have : IsDominant h.fromNormalization := by
    have : IsDominant (h.toNormalization ≫ h.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp h.toNormalization h.fromNormalization
  have hs : Surjective h.fromNormalization :=
    surjective_of_isDominant_of_isClosed_range _ h.fromNormalization.isClosedMap.isClosed_range
  have hdim : topologicalKrullDim h.normalization = (Y.dim + 1 : ℕ) := by
    rw [← V.ar.dim_eq]
    refine le_antisymm (ProperCover.dim_le_of_residueDegree_pos h.fromNormalization
      (apply_genericPoint_of_isDominant h.fromNormalization) ?_)
      (PosBaseChange.dim_le_of_isClosedMap h.fromNormalization.isClosedMap hs.surj)
    let := (h.fromNormalization.residueFieldMap (genericPoint h.normalization)).hom.toAlgebra
    have : Module.Finite (V.X.residueField (h.fromNormalization (genericPoint h.normalization)))
        (h.normalization.residueField (genericPoint h.normalization)) :=
      residueFieldMap_finite_of_locallyQuasiFinite h.fromNormalization _
    exact Module.finrank_pos
  have hfl : Flat (h.fromNormalization ≫ V.p) :=
    GlobalTheory.flat_fromNormalization_comp h F V.p (g ≫ V.π ≫ Y.str) w
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have : Surjective g := surjective_of_isDominant_of_isClosed_range _ g.isClosedMap.isClosed_range
  have hη : (g ≫ V.π) (genericPoint G) ⤳ genericPoint Y.X :=
    specializes_of_eq (apply_genericPoint_of_isDominant (g ≫ V.π))
  let W : Cover Y :=
    { X := h.normalization
      p := h.fromNormalization ≫ V.p
      ar := ⟨V.ar.isDomain, V.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin V.ar.isProjOver,
        inferInstance, hdim⟩
      normal := GlobalTheory.IsNormalScheme.pred _
      G := G
      j := h.toNormalization
      π := g ≫ V.π
      pb := by simpa [Category.assoc] using hpb.paste_vert V.pb
      φ := SmallSec.fnMap (g ≫ V.π) hη
      φ_spec := by
        change _ = Spec.map (Y.X.presheaf.stalkSpecializes hη ≫ (g ≫ V.π).stalkMap _) ≫ _
        rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
          Scheme.SpecMap_stalkMap_fromSpecStalk] }
  exact ⟨W, h.fromNormalization, k, rfl, ⟨g, by simp [W, h], rfl⟩, hk⟩

end GlobalTheory.Mean4O.NormCoverFin
