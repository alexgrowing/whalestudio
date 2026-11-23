import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClosedImmFieldDescent

set_option backward.isDefEq.respectTransparency.types false

theorem isClosedImmersion_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@IsClosedImmersion : MorphismProperty Scheme.{0})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have := GlobalTheory.isAffineHom_descendsAlong_fpqc.{0}
  have hP : HasAffineProperty @IsClosedImmersion (affineAnd fun f ↦ Function.Surjective f) :=
    IsClosedImmersion.hasAffineProperty
  have H₂ : ∀ {R S : CommRingCat.{0}} {f : R ⟶ S}, (@Surjective ⊓ @Flat) (Spec.map f) →
      RingHom.FaithfullyFlat f.hom := by
    intro R S f ⟨hf₁, hf₂⟩
    rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
    refine ⟨?_, (Spec.map f).surjective⟩
    rwa [HasRingHomProperty.Spec_iff (P := @Flat)] at hf₂
  refine IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact _ _ ?_ ?_
  · rw [inf_comm]
    exact inf_le_inf le_rfl (IsLocalIso.le_of_isZariskiLocalAtSource _)
  intro R S Y φ g h hf
  have : IsAffine Y := by
    have : IsAffineHom g := MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ⟨h, inferInstance⟩
      (HasAffineProperty.affineAnd_le_isAffineHom @IsClosedImmersion hP _ hf)
    exact isAffine_of_isAffineHom g
  wlog hY : ∃ S, Y = Spec S generalizing Y
  · rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) Y.isoSpec.inv]
    have heq : pullback.fst (Spec.map φ) (Y.isoSpec.inv ≫ g) =
        pullback.map _ _ _ _ (𝟙 _) (Y.isoSpec.inv) (𝟙 _) (by simp) (by simp) ≫
          pullback.fst (Spec.map φ) g := (pullback.lift_fst _ _ _).symm
    refine this _ ?_ inferInstance ⟨_, rfl⟩
    rwa [heq, MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)]
  obtain ⟨Y, rfl⟩ := hY
  apply of_pullback_fst_Spec_of_codescendsAlong _ _ RingHom.FaithfullyFlat.codescendsAlong_surjective H₂ _ h hf
  intro R' S' f'
  exact HasAffineProperty.SpecMap_iff_of_affineAnd hP RingHom.surjective_respectsIso f'

theorem isPullback_baseChange_step {R k Ω : Type} [CommRing R] [Field k] [Field Ω] [Algebra R k]
    [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] {C : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of R)) :
    IsPullback (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))
      (pullback.map c (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) c (Spec.map (CommRingCat.ofHom (algebraMap R k)))
        (𝟙 C) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]))
      (Spec.map (CommRingCat.ofHom (algebraMap k Ω)))
      (pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap R k)))) := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R k)) =
      Spec.map (CommRingCat.ofHom (algebraMap R Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm (IsPullback.of_hasPullback c _).flip
  have h0 := (IsPullback.of_hasPullback c (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))).flip
  rw [pullback.lift_fst, Category.comp_id, e]
  exact h0

theorem fpqc_specMap_field (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω] :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) := by
  refine ⟨⟨⟨fun x ↦ ?_⟩, ?_⟩, inferInstance⟩
  · obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
    exact ⟨y, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩
  · rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem isClosedImmersion_of_baseChange_extension :
    ∀ (R k Ω : Type) [CommRing R] [Field k] [Field Ω] [Algebra R k] [Algebra k Ω] [Algebra R Ω] [IsScalarTower R k Ω] (V W : Over (Spec (CommRingCat.of R))) (f : V ⟶ W), IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f).left → IsClosedImmersion ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f).left := by
  intro R k Ω _ _ _ _ _ _ _ V W f hΩ
  have hd := isClosedImmersion_descendsAlong_fpqc
  have e : (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ≫ (Spec.map (CommRingCat.ofHom (algebraMap R k))) = (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let vX := pullback.map V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (𝟙 _) (by simp) (by rw [Category.comp_id, e])
  let vY := pullback.map W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (𝟙 _) (by simp) (by rw [Category.comp_id, e])
  have sX : IsPullback (pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) vX (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k)))) :=
    isPullback_baseChange_step (k := k) (Ω := Ω) V.hom
  have sY : IsPullback (pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω)))) vY (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) (pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k)))) :=
    isPullback_baseChange_step (k := k) (Ω := Ω) W.hom
  let φk := ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R k).map f).left
  let φΩ := ((GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.baseChange R Ω).map f).left
  have hk2 : φk ≫ pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) = pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) := by simp only [φk, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have hk1 : φk ≫ pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) = pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R k))) ≫ f.left := by simp only [φk, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have hΩ2 : φΩ ≫ pullback.snd W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) = pullback.snd V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) := by simp only [φΩ, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have hΩ1 : φΩ ≫ pullback.fst W.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) = pullback.fst V.hom (Spec.map (CommRingCat.ofHom (algebraMap R Ω))) ≫ f.left := by simp only [φΩ, Over.pullback_map_left, pullback.lift_fst, pullback.lift_snd, Category.comp_id, Category.assoc]
  have comm : φΩ ≫ vY = vX ≫ φk := by
    apply pullback.hom_ext
    · simp only [vX, vY, Category.assoc, hk1, pullback.lift_fst, pullback.lift_fst_assoc, Category.comp_id]
      exact hΩ1
    · simp only [vX, vY, Category.assoc, hk2, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
      rw [← Category.assoc, hΩ2]
  have sq : IsPullback φΩ vX vY φk := by
    refine IsPullback.of_right ?_ comm sY
    rw [hΩ2, hk2]
    exact sX
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sq
    (MorphismProperty.of_isPullback (P := @Surjective ⊓ @Flat ⊓ @QuasiCompact) sY (fpqc_specMap_field k Ω)) hΩ

end GlobalTheory.ClosedImmFieldDescent
