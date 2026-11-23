import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjectiveStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreAmple

variable {S X T₁ T₂ X₁ X₂ : Scheme.{0}} {f : X ⟶ S} {M : LB X} {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ T₁} {t₁ : T₁ ⟶ S}
  {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ T₂} {t₂ : T₂ ⟶ S}

theorem exists_isPullback (h₁ : IsPullback π₁ f₁ f t₁) (h₂ : IsPullback π₂ f₂ f t₂) (u : T₂ ⟶ T₁)
    (hu : u ≫ t₁ = t₂) : ∃ φ : X₂ ⟶ X₁, π₂ = φ ≫ π₁ ∧ IsPullback φ f₂ f₁ u := by
  have w : π₂ ≫ f = (f₂ ≫ u) ≫ t₁ := by rw [Category.assoc, hu, h₂.w]
  refine ⟨h₁.lift _ _ w, (h₁.lift_fst _ _ _).symm, IsPullback.of_right ?_ (h₁.lift_snd _ _ _) h₁⟩
  rw [h₁.lift_fst, hu]
  exact h₂

theorem lbIso_pull_comp {φ : X₂ ⟶ X₁} (hφ : π₂ = φ ≫ π₁) {L₁ : LB X₁} (e : LBIso L₁ (M.pull π₁)) :
    LBIso (M.pull π₂) (L₁.pull φ) :=
  LBIso.chartPull (chartPullSame M (fun _ : PUnit => π₂) (fun _ => π₁) (fun _ => 1) φ fun _ => hφ)
    (Geo.Tor.chartPullPull L₁ φ φ rfl) e.symm

theorem lbIso_pull_pull (hM : M.IsLB) (φ : X₂ ⟶ X₁) (π₁ : X₁ ⟶ X) :
    LBIso ((M.pull π₁).pull φ) (M.pull (φ ≫ π₁)) :=
  (lbIso_pull_comp rfl (GlobalTheory.lbIso_refl (pull_isLB hM π₁))).symm

theorem relAmple_of_factor [IsProper f] (hM : M.IsLB) (h₁ : IsPullback π₁ f₁ f t₁) (h₂ : IsPullback π₂ f₂ f t₂)
    (u : T₂ ⟶ T₁) (hu : u ≫ t₁ = t₂) {L₁ : LB X₁} (hL₁ : L₁.IsLB) (e : LBIso L₁ (M.pull π₁))
    (hA : Out.RelAmple (Over.mk f₁) L₁) : Out.RelAmple (Over.mk f₂) (M.pull π₂) := by
  obtain ⟨φ, hφ, H⟩ := exists_isPullback h₁ h₂ u hu
  have hp : IsProper (Over.mk f₂).hom := MorphismProperty.of_isPullback (P := @IsProper) h₂ ‹_›
  refine AmpleLocal.relAmple_of_locally T₂ (Over.mk f₂) (M.pull π₂) (pull_isLB hM π₂)
    inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := T₁) (U := ⊤) (x := u s) trivial
  exact ⟨u ⁻¹ᵁ V, hs, PolPull.relAmple_restrict (G := Over.mk f₁) (G' := Over.mk f₂) H hL₁ (pull_isLB hM π₂)
    (lbIso_pull_comp hφ e) hA V hV⟩

theorem relAmple_of_fieldExtension [IsProper f] (hM : M.IsLB) {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K)
    {f₁ : X₁ ⟶ Sp K₀} {t₁ : Sp K₀ ⟶ S} {f₂ : X₂ ⟶ Sp K} (h₁ : IsPullback π₁ f₁ f t₁)
    (h₂ : IsPullback π₂ f₂ f (spMap i ≫ t₁)) {L₁ : LB X₁} (hL₁ : L₁.IsLB) (e : LBIso L₁ (M.pull π₁))
    (hA : Out.RelAmple (Over.mk f₂) (M.pull π₂)) : Out.RelAmple (Over.mk f₁) L₁ := by
  obtain ⟨φ, hφ, H⟩ := exists_isPullback h₁ h₂ _ rfl
  have : Subsingleton (Spec (CommRingCat.of K₀)) := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
  have : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have : Flat (Out.specOf i) := inferInstance
  have : Surjective (Out.specOf i) := inferInstance
  have hp : IsProper f₁ := MorphismProperty.of_isPullback (P := @IsProper) h₁ ‹_›
  have : IsProper (Over.mk f₁).hom := hp
  have : IsProper f₂ := MorphismProperty.of_isPullback (P := @IsProper) h₂ ‹_›
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  have : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated f₁
  refine (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f₁) hL₁).2 (AmpleDescent.isAmpleLB_of_pull i H hL₁ ?_)
  exact (isAmpleLB_of_relAmple_of_isAffine (Over.mk f₂) (pull_isLB hM π₂) hA).of_lbIso (LB.isLB_pull hL₁ φ)
    (lbIso_pull_comp hφ e).symm

theorem residueField_fraction {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime] (y : p.ResidueField) :
    ∃ a b : R, algebraMap R p.ResidueField b ≠ 0 ∧
      y * algebraMap R p.ResidueField b = algebraMap R p.ResidueField a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ p) y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hb' : algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p b) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩

theorem relAmple_of_geometricFibres : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), Out.RelAmple (Over.mk (pullback.snd P.A.hom y)) (M.pull (pullback.fst P.A.hom y))) → Out.RelAmple P.A M := by
  intro _ S _ P M hM hfib
  have := P.isAb.proper
  have := P.isAb.smooth
  refine AmpleLocal.relAmple_of_locally S P.A M hM inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := s) trivial
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let t : Spec (CommRingCat.of Γ(S, V)) ⟶ S := hV.fromSpec
  obtain ⟨p, hp⟩ : s ∈ Set.range t := by rw [hV.range_fromSpec]; exact hs
  have hB := IsPullback.of_hasPullback P.A.hom t
  have hL := pull_isLB hM (pullback.fst P.A.hom t)
  have := p.isPrime
  let g := algebraMap Γ(S, V) p.asIdeal.ResidueField
  let i := algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
  obtain ⟨r, hr, hA⟩ := GlobalTheory.T.relAmple_near_fibre_flat_projective Γ(S, V) (Over.mk (pullback.snd P.A.hom t)) (M.pull (pullback.fst P.A.hom t))
    (inferInstanceAs (Flat (pullback.snd P.A.hom t)))
    (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S P.A P.L P.isAb P.isLB P.ample _ t _ _ _ hB).1
    hL _ g (residueField_fraction p.asIdeal)
    (relAmple_of_fieldExtension hM i
      ((IsPullback.of_hasPullback (pullback.snd P.A.hom t) (spMap g)).paste_horiz hB)
      (IsPullback.of_hasPullback P.A.hom _) (pull_isLB hL _) (lbIso_pull_pull hM _ _) (hfib _ _))
  let D : (Spec (CommRingCat.of Γ(S, V))).Opens := PrimeSpectrum.basicOpen r
  have hD : p ∈ D := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
  have hrange : Set.range (t ''ᵁ D).ι ⊆ Set.range (D.ι ≫ t) := by
    rintro _ ⟨⟨_, x, hx, rfl⟩, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨t ''ᵁ D, ⟨p, hD, hp⟩, ?_⟩
  exact relAmple_of_factor hM ((IsPullback.of_hasPullback (pullback.snd P.A.hom t) D.ι).paste_horiz hB)
    (isPullback_morphismRestrict P.A.hom (t ''ᵁ D)).flip (IsOpenImmersion.lift (D.ι ≫ t) _ hrange)
    (IsOpenImmersion.lift_fac _ _ _) (pull_isLB hL _) (lbIso_pull_pull hM _ _) hA

end GlobalTheory.FibreAmple
