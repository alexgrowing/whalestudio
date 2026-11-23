import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleDescentToSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFieldExtensionBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section

namespace GlobalTheory.ProjFinite

theorem exists_relAmple_of_isProjBy {R : Type} [CommRing R] {A : Over (Sp R)} (h : GlobalTheory.AbLaw.IsProjBy A.hom) :
    ∃ H : LB A.left, H.IsLB ∧ Out.RelAmple A H := by
  obtain ⟨H, hH, m, s, hs⟩ := h
  have e : GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ) = H := by
    cases H
    simp [GlobalTheory.AbLaw.pw]
  have k : ∀ s : Fin (m + 1) → LB.Sec (GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ)),
      GlobalTheory.AbLaw.VeryAmpleBy A.hom (GlobalTheory.AbLaw.pw H ((1 : ℕ) : ℤ)) s → Out.RelAmple A H :=
    fun s hs => GlobalTheory.Unif.relAmple_of_veryAmpleBy hH le_rfl s hs
  rw [e] at k
  exact ⟨H, hH, k s hs⟩

theorem isProjBy_of_fieldExtension {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) {A₀ : Over (Sp K₀)}
    {A : Over (Sp K)} [IsProper A₀.hom] {φ : A.left ⟶ A₀.left} (h : IsPullback φ A.hom A₀.hom (spMap i))
    {L₀ : LB A₀.left} {L : LB A.left} (hL₀ : L₀.IsLB) (hL : L.IsLB) (hw : LBIso L (L₀.pull φ))
    (hA : Out.RelAmple A L) : GlobalTheory.AbLaw.IsProjBy A₀.hom := by
  have : Subsingleton (Spec (CommRingCat.of K₀)) := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
  have : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have : Flat (Out.specOf i) := inferInstance
  have : Surjective (Out.specOf i) := inferInstance
  have : IsProper A.hom := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  have : CompactSpace A₀.left := QuasiCompact.compactSpace_of_compactSpace A₀.hom
  have : QuasiSeparatedSpace A₀.left := quasiSeparatedSpace_of_quasiSeparated A₀.hom
  have h₀ : Out.RelAmple A₀ L₀ :=
    (relAmple_iff_isAmpleLB_of_isAffine A₀ hL₀).2 (AmpleDescent.isAmpleLB_of_pull i h hL₀
      ((isAmpleLB_of_relAmple_of_isAffine A hL hA).of_lbIso (LB.isLB_pull hL₀ φ) hw.symm))
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K₀ A₀ L₀ hL₀).1 h₀
  exact ⟨_, GlobalTheory.AbLaw.isLB_pw hL₀ d, n, s, hs⟩

theorem exists_isPullback {S X T₁ T₂ X₁ X₂ : Scheme.{0}} {f : X ⟶ S} {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ T₁} {t₁ : T₁ ⟶ S}
    {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ T₂} {t₂ : T₂ ⟶ S} (h₁ : IsPullback π₁ f₁ f t₁) (h₂ : IsPullback π₂ f₂ f t₂)
    (u : T₂ ⟶ T₁) (hu : u ≫ t₁ = t₂) : ∃ φ : X₂ ⟶ X₁, φ ≫ π₁ = π₂ ∧ IsPullback φ f₂ f₁ u := by
  have w : π₂ ≫ f = (f₂ ≫ u) ≫ t₁ := by rw [Category.assoc, hu, h₂.w]
  refine ⟨h₁.lift _ _ w, h₁.lift_fst _ _ _, IsPullback.of_right ?_ (h₁.lift_snd _ _ _) h₁⟩
  rw [h₁.lift_fst, hu]
  exact h₂

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_finite_isProjBy : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L), GlobalTheory.AbLaw.IsProjBy ((Over.pullback (spMap (algebraMap K L))).obj A).hom := by
  intro K _ A _ hA
  have := hA.proper
  have := hA.comm
  let Ω := AlgebraicClosure K
  let a : K →+* Ω := algebraMap K Ω
  let B : Over (Sp Ω) := (Over.pullback (spMap a)).obj A
  have sqB : IsPullback (pullback.fst A.hom (spMap a)) B.hom A.hom (spMap a) := IsPullback.of_hasPullback _ _
  have hB : IsAbelianScheme B :=
    { comm := inferInstance
      smooth := MorphismProperty.of_isPullback (P := @Smooth) sqB hA.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) sqB hA.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) sqB hA.geomConnected }
  obtain ⟨H, hH, hamp⟩ := exists_relAmple_of_isProjBy
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme Ω B hB)
  let K₀ : Subfield Ω := a.fieldRange
  let j : K →+* K₀ := a.rangeRestrictField
  have sq₀ := IsPullback.of_hasPullback A.hom (spMap j)
  obtain ⟨φ, hφ, sq⟩ := exists_isPullback sq₀ sqB (spMap K₀.subtype) (spMap_comp _ _)
  obtain ⟨s, hs⟩ := GlobalTheory.LBDescent.exists_lb_subfield Ω K₀ _ _ _ _ φ H hH sq
  let L : IntermediateField K Ω := IntermediateField.adjoin K (s : Set Ω)
  have hfin : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have h : K₀ ≤ L.toSubfield := by
    rintro _ ⟨x, rfl⟩
    exact L.algebraMap_mem x
  refine ⟨L, inferInstance, inferInstance, hfin, ?_⟩
  let C : Over (Sp L) := (Over.pullback (spMap (algebraMap K L))).obj A
  have sqC : IsPullback (pullback.fst A.hom (spMap (algebraMap K L))) C.hom A.hom (spMap (algebraMap K L)) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨φ₁, hφ₁, sq₁⟩ := exists_isPullback sq₀ sqC (spMap (Subfield.inclusion h)) (spMap_comp _ _)
  obtain ⟨ψ, hψ, sq₂⟩ := exists_isPullback sqC sqB (spMap L.toSubfield.subtype) (spMap_comp _ _)
  obtain ⟨L₁, hL₁, hw⟩ := hs L.toSubfield h (IntermediateField.subset_adjoin K _) C.left C.hom φ₁ ψ sq₁
    (sq₀.hom_ext (by rw [Category.assoc, hφ₁, hψ, hφ]) (by
      rw [Category.assoc, sq₁.w, ← Category.assoc, sq₂.w, Category.assoc, sq.w]
      exact congrArg _ (spMap_comp _ _))) sq₂.w
  have : IsProper C.hom := MorphismProperty.of_isPullback (P := @IsProper) sqC hA.proper
  exact isProjBy_of_fieldExtension L.toSubfield.subtype sq₂ hL₁ hH hw hamp

end GlobalTheory.ProjFinite

end
