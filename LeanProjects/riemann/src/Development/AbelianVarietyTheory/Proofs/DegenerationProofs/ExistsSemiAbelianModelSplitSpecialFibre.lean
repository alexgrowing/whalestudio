import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SplitReduction

open IsLocalRing

variable {p : ℕ} [Fact p.Prime]

noncomputable def residueEmb (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] :
    ResidueField (integralClosure ℤ_[p] K) →+* GlobalTheory.ZJ.kb p :=
  haveI := isLocalHom_integralClosureToPadicAlgClIntegers K
  ResidueField.map (integralClosureToPadicAlgClIntegers K)

noncomputable def intIncl {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') :
    integralClosure ℤ_[p] K →+* integralClosure ℤ_[p] K' :=
  ((IntermediateField.inclusion h).restrictScalars ℤ_[p]).mapIntegralClosure

instance isLocalHom_intIncl {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') : IsLocalHom (intIncl h) :=
  isLocalHom_of_injective_integralClosure _ (mapIntegralClosure_padicInt_injective (IntermediateField.inclusion h))

theorem exists_subset_range (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (s : Set (GlobalTheory.ZJ.kb p)) (hs : s.Finite) :
    ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : K ≤ K') (_ : FiniteDimensional ℚ_[p] K'),
      s ⊆ Set.range (residueEmb K') := by
  choose l hl using residue_surjective (R := GlobalTheory.ZJ.OO p)
  let t : Set (PadicAlgCl p) := (fun x => (l x : PadicAlgCl p)) '' s
  haveI : Finite t := (hs.image _).to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] t) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨K ⊔ IntermediateField.adjoin ℚ_[p] t, le_sup_left, inferInstance, fun x hx => ?_⟩
  have hm : (l x : PadicAlgCl p) ∈ K ⊔ IntermediateField.adjoin ℚ_[p] t :=
    (le_sup_right : IntermediateField.adjoin ℚ_[p] t ≤ _) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
  refine ⟨residue _ ⟨⟨_, hm⟩, (mem_integralClosure_padicInt_iff _ _).2
    ((mem_padicAlgCl_valuationSubring_iff_norm_le_one _).1 (l x).2)⟩, ?_⟩
  exact hl x

theorem residueEmb_comp {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K'] (h : K ≤ K') :
    (residueEmb K').comp (ResidueField.map (intIncl h)) = residueEmb K :=
  RingHom.ext fun x => by
    obtain ⟨x, rfl⟩ := residue_surjective x
    exact congrArg (residue (GlobalTheory.ZJ.OO p)) (Subtype.ext rfl)

theorem algebraMap_comp_intIncl {K K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') :
    (IntermediateField.inclusion h).toRingHom.comp (algebraMap (integralClosure ℤ_[p] K) K) =
      (algebraMap (integralClosure ℤ_[p] K') K').comp (intIncl h) :=
  RingHom.ext fun _ => rfl

theorem spMap_comp {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (a : R →+* R₁) (b : R₁ →+* R₂) :
    spMap b ≫ spMap a = spMap (b.comp a) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_iso_of_square {R R₁ R₂ T : Type} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing T]
    {a : R →+* R₁} {b : R₁ →+* T} {c : R →+* R₂} {d : R₂ →+* T} (e : b.comp a = d.comp c)
    (G : Over (Sp R)) [GrpObj G] :
    ∃ i : (Over.pullback (spMap b)).obj ((Over.pullback (spMap a)).obj G) ≅
      (Over.pullback (spMap d)).obj ((Over.pullback (spMap c)).obj G), IsMonHom i.hom := by
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback ((Over.pullback (spMap a)).obj G) (spMap b)).comp
      (isGrpPullback_pullback G _)).congr (by rw [spMap_comp, e, ← spMap_comp]) rfl)
    ((isGrpPullback_pullback ((Over.pullback (spMap c)).obj G) (spMap d)).comp (isGrpPullback_pullback G _))
  exact ⟨i, hi⟩

theorem exists_finite_torusExtension_specialFibre {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] [IsAlgClosed Ω]
    (σ : ResidueField R →+* Ω) (G : Over (Sp R)) [GrpObj G] (hG : IsSemiAbelian G) :
    ∃ s : Set Ω, s.Finite ∧ ∀ (R' : Type) [CommRing R'] [IsLocalRing R'] (f : R →+* R') [IsLocalHom f]
      (β : ResidueField R' →+* Ω), β.comp (ResidueField.map f) = σ → s ⊆ Set.range β →
      ∃ E : SplitExt (Sp (ResidueField R')),
        E.IsGt ((Over.pullback (spMap (residue R'))).obj ((Over.pullback (spMap f)).obj G)) := by
  have h₀ : IsSemiAbelian ((Over.pullback (spMap (residue R))).obj G) := IsSemiAbelian.pullback _ G hG
  haveI := h₀.smooth
  haveI := h₀.quasiCompact
  haveI := h₀.separated
  obtain ⟨T⟩ := h₀.fibres _ (spMap σ)
  obtain ⟨s, hs, H⟩ := FieldModel.exists_finite_torusExtension_range σ _ T
  refine ⟨s, hs, fun R' _ _ f _ β hβ hr => ?_⟩
  obtain ⟨T'⟩ := H _ (ResidueField.map f) β hβ hr
  obtain ⟨i, hi⟩ := exists_iso_of_square (ResidueField.map_comp_residue f) G
  haveI := hG.comm
  exact exists_splitExt_isGt_of_torusExtension _ _ ⟨torusExtOfIso i T'⟩

theorem exists_isGrpPullback_of_square {R R₁ R₂ T K : Type} [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing T]
    [CommRing K] {a : R →+* R₁} {b : R₁ →+* T} {c : R →+* R₂} {d : R₂ →+* T} (e : b.comp a = d.comp c)
    {u : K →+* R₁} {v : K →+* T} (e' : b.comp u = v) (G : Over (Sp R)) [GrpObj G] (A : Over (Sp K)) [GrpObj A]
    {φ : pullback G.hom (spMap a) ⟶ A.left} (hφ : IsGrpPullback ((Over.pullback (spMap a)).obj G) A (spMap u) φ) :
    ∃ ψ : pullback ((Over.pullback (spMap c)).obj G).hom (spMap d) ⟶ A.left,
      IsGrpPullback ((Over.pullback (spMap d)).obj ((Over.pullback (spMap c)).obj G)) A (spMap v) ψ := by
  obtain ⟨i, hi⟩ := exists_iso_of_square e.symm G
  exact ⟨_, ((isGrpPullback_of_iso i).comp ((isGrpPullback_pullback _ (spMap b)).comp hφ)).congr
    (by rw [Category.id_comp, spMap_comp, e']) rfl⟩

end GlobalTheory.SplitReduction

namespace GlobalTheory

open SplitReduction in

theorem exists_semiAbelian_model_split_specialFibre : GlobalTheory.Published.SemistableReductionSt → ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K] (P : Out.PolAV (Sp K)), ∃ (K' : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ K') (_ : IsLocalRing (integralClosure ℤ_[p] K')), FiniteDimensional ℚ_[p] K' ∧ ∃ (G : Over (Sp (integralClosure ℤ_[p] K'))) (_ : GrpObj G), IsSemiAbelian G ∧ (∃ E : SplitExt (Sp (IsLocalRing.ResidueField (integralClosure ℤ_[p] K'))), E.IsGt ((Over.pullback (spMap (IsLocalRing.residue (integralClosure ℤ_[p] K')))).obj G)) ∧ ∃ φ : pullback G.hom (spMap (algebraMap (integralClosure ℤ_[p] K') K')) ⟶ P.A.left, IsGrpPullback ((Over.pullback (spMap (algebraMap (integralClosure ℤ_[p] K') K'))).obj G) P.A (spMap (IntermediateField.inclusion h).toRingHom) φ := by
  intro H p _ K _ P
  obtain ⟨K₁, h₁, f₁, G, gG, hG, φ, hφ⟩ := H p K P
  haveI := GlobalTheory.ZJ.isAlgClosed_kb (p := p)
  obtain ⟨s, hs, T⟩ := exists_finite_torusExtension_specialFibre (residueEmb K₁) G hG
  obtain ⟨K', h, f', hr⟩ := exists_subset_range K₁ s hs
  exact ⟨K', h₁.trans h, inferInstance, f', (Over.pullback (spMap (intIncl h))).obj G, inferInstance,
    IsSemiAbelian.pullback _ G hG, T _ (intIncl h) (residueEmb K') (residueEmb_comp h) hr,
    exists_isGrpPullback_of_square (algebraMap_comp_intIncl h) (RingHom.ext fun _ => rfl) G P.A hφ⟩

end GlobalTheory
