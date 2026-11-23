import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtAbelianVarietyHomDescentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.ArcPull GlobalTheory.ArcQ

namespace GlobalTheory.IsoFinExt

theorem isPullback_compare {X S L S' T : Scheme.{0}} (a : X ⟶ S) (b : L ⟶ S) (i : S' ⟶ S) (j : T ⟶ L)
    (l : T ⟶ S') (hc : l ≫ i = j ≫ b) :
    ∃ q : pullback (pullback.snd a b) j ⟶ pullback a i,
      q ≫ pullback.fst a i = pullback.fst _ _ ≫ pullback.fst a b ∧
      IsPullback q (pullback.snd _ _) (pullback.snd a i) l := by
  have hw : (pullback.fst (pullback.snd a b) j ≫ pullback.fst a b) ≫ a = (pullback.snd _ _ ≫ l) ≫ i := by
    rw [Category.assoc, pullback.condition, pullback.condition_assoc, Category.assoc, hc]
  refine ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, ?_⟩
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback a i)
  rw [pullback.lift_fst, hc]
  exact (IsPullback.of_hasPullback (pullback.snd a b) j).paste_horiz (IsPullback.of_hasPullback a b)

theorem isIso_of_compare {X₁ X₂ S L S' T : Scheme.{0}} (a₁ : X₁ ⟶ S) (a₂ : X₂ ⟶ S) (b : L ⟶ S) (i : S' ⟶ S)
    (j : T ⟶ L) (l : T ⟶ S') [Surjective l] [Flat l] [QuasiCompact l] (hc : l ≫ i = j ≫ b)
    (f : pullback a₁ b ⟶ pullback a₂ b) [IsIso f] (hf : f ≫ pullback.snd _ _ = pullback.snd _ _)
    (f' : pullback a₁ i ⟶ pullback a₂ i) (hf' : f' ≫ pullback.snd _ _ = pullback.snd _ _)
    (h : ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback a₁ b) (p' : Z ⟶ pullback a₁ i) (t : Z ⟶ T),
      p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ j →
      p' ≫ pullback.snd _ _ = t ≫ l → p ≫ f ≫ pullback.fst _ _ = p' ≫ f' ≫ pullback.fst _ _) :
    IsIso f' := by
  obtain ⟨q₁, e₁, H₁⟩ := isPullback_compare a₁ b i j l hc
  obtain ⟨q₂, e₂, H₂⟩ := isPullback_compare a₂ b i j l hc
  let F : pullback (pullback.snd a₁ b) j ⟶ pullback (pullback.snd a₂ b) j :=
    pullback.map _ _ _ _ f (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hf]) (by simp)
  have hF₁ : F ≫ pullback.fst _ _ = pullback.fst _ _ ≫ f := pullback.lift_fst _ _ _
  have hF₂ : F ≫ pullback.snd _ _ = pullback.snd _ _ := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hw : q₁ ≫ f' = F ≫ q₂ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, e₂, ← Category.assoc F, hF₁, Category.assoc]
      exact (h _ _ q₁ _ e₁.symm pullback.condition H₁.w).symm
    · rw [Category.assoc, Category.assoc, hf', H₂.w, ← Category.assoc, hF₂, H₁.w]
  have H : IsPullback q₁ F f' q₂ := by
    refine IsPullback.of_bot ?_ hw H₂
    rw [hF₂, hf']
    exact H₁
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) q₂ :=
    ⟨⟨MorphismProperty.of_isPullback H₂.flip ‹Surjective l›,
      MorphismProperty.of_isPullback H₂.flip ‹Flat l›⟩,
      MorphismProperty.of_isPullback H₂.flip ‹QuasiCompact l›⟩
  have hF : IsIso F := inferInstance
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
    H.flip hq hF

theorem exists_finite_iso : ∀ (K L : Type) [Field K] [CharZero K] [Field L] (β : K →+* L) (A₁ A₂ : Over (Sp K)) [GrpObj A₁] [GrpObj A₂], IsAbelianScheme A₁ → IsAbelianScheme A₂ → ∀ (f : (Over.pullback (spMap β)).obj A₁ ≅ (Over.pullback (spMap β)).obj A₂), IsMonHom f.hom → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω : Type) (_ : Field Ω) (j : L →+* Ω) (l : K' →+* Ω) (φ : (Over.pullback (spMap io)).obj A₁ ≅ (Over.pullback (spMap io)).obj A₂), io.Finite ∧ l.comp io = j.comp β ∧ IsMonHom φ.hom ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback A₁.hom (spMap β)) (p' : Z ⟶ pullback A₁.hom (spMap io)) (t : Z ⟶ Sp Ω), p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ spMap j → p' ≫ pullback.snd _ _ = t ≫ spMap l → p ≫ f.hom.left ≫ pullback.fst _ _ = p' ≫ φ.hom.left ≫ pullback.fst _ _ := by
  intro K L _ _ _ β A₁ A₂ _ _ h₁ h₂ f hf
  obtain ⟨K', _, io, Ω, _, j, l, f', hfin, hc, hm, h⟩ := GlobalTheory.T.exists_finiteExt_abelianVarietyHom_descent K L β A₁ A₂ h₁ h₂ f.hom hf
  have hc' : spMap l ≫ spMap io = spMap j ≫ spMap β := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hc]
  have : Flat (spMap l) := by
    rw [Flat.SpecMap_iff]
    letI := l.toAlgebra
    exact (inferInstance : Module.Flat K' Ω)
  have : Surjective (spMap l) := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  have hl : IsIso f.hom.left := inferInstanceAs (IsIso ((Over.forget _).map f.hom))
  have : IsIso f'.left :=
    @isIso_of_compare _ _ _ _ _ _ A₁.hom A₂.hom (spMap β) (spMap io) (spMap j) (spMap l) _ _ _ hc'
      f.hom.left hl (Over.w f.hom) f'.left (Over.w f') h
  have : IsIso ((Over.forget _).map f') := this
  have : IsIso f' := isIso_of_reflects_iso f' (Over.forget _)
  exact ⟨K', inferInstance, io, Ω, inferInstance, j, l, asIso f', hfin, hc, hm, h⟩

end GlobalTheory.IsoFinExt
