import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RingHomFlatCodescendsAlongFaithfullyFlat

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hypotheses₂

namespace FreeQuot

universe u

def IsFiniteLocallyFree {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  IsFinite f ∧ Flat f ∧ LocallyOfFinitePresentation f

variable {S : Scheme.{u}} (G X : Over S) [GrpObj G] [ModObj G X]

def IsFreeAction : Prop :=
  ∀ (T : Over S) (g : T ⟶ G) (x : T ⟶ X), g • x = x → g = 1

def orbit (x : X.left) : Set X.left :=
  (γ[G, X] : G ⊗ X ⟶ X).left '' ((snd G X).left ⁻¹' {x})

def orbitPresheaf : (Over S)ᵒᵖ ⥤ Type u where
  obj T := MulAction.orbitRel.Quotient (T.unop ⟶ G) (T.unop ⟶ X)
  map f := ↾(Quotient.map (fun x => f.unop ≫ x) (by
    rintro _ y ⟨g, rfl⟩
    exact ⟨f.unop ≫ g, (ModObj.comp_smul _ _ _).symm⟩))
  map_id T := by
    ext ⟨x⟩
    exact congrArg (Quotient.mk _) (Category.id_comp x)
  map_comp f g := by
    ext ⟨x⟩
    exact congrArg (Quotient.mk _) (Category.assoc _ _ x)

variable {X} {Y : Over S}

def IsInvariant (q : X ⟶ Y) : Prop :=
  (γ[G, X] : G ⊗ X ⟶ X) ≫ q = snd G X ≫ q

variable {G} in
theorem IsInvariant.smul_comp {q : X ⟶ Y} (h : IsInvariant G q) {T : Over S} (g : T ⟶ G) (x : T ⟶ X) :
    (g • x) ≫ q = x ≫ q := by
  rw [Hom.smul_def, Category.assoc, h, lift_snd_assoc]

variable {G} in

def IsInvariant.desc {q : X ⟶ Y} (h : IsInvariant G q) : orbitPresheaf G X ⟶ yoneda.obj Y where
  app T := ↾(Quotient.lift (fun x => x ≫ q) (by
    rintro _ y ⟨g, rfl⟩
    exact h.smul_comp g y))
  naturality T T' f := by
    ext ⟨x⟩
    exact Category.assoc _ _ _

def IsFppfQuotient (q : X ⟶ Y) : Prop :=
  ∃ h : IsInvariant G q,
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) h.desc ∧
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) h.desc

def IsFppfTorsor (q : X ⟶ Y) : Prop :=
  IsPullback (γ[G, X] : G ⊗ X ⟶ X) (snd G X) q q ∧
    ∃ (J : Type u) (U : J → Scheme.{u}) (f : ∀ i, U i ⟶ Y.left),
      (∀ i, Flat (f i) ∧ LocallyOfFinitePresentation (f i)) ∧ (∀ y : Y.left, ∃ i z, f i z = y) ∧
        ∀ i, ∃ s : U i ⟶ X.left, s ≫ q.left = f i

end FreeQuot

open FreeQuot

def FreeQuotientScheme : Prop :=
  ∀ (S : Scheme.{0}) (G X : Over S) [GrpObj G] [ModObj G X],
    IsFiniteLocallyFree G.hom → IsFreeAction G X →
    (∀ x : X.left, ∃ U : X.left.Opens, IsAffineOpen U ∧ orbit G X x ⊆ U) →
    ∃ (Y : Over S) (q : X ⟶ Y), IsFppfQuotient G q ∧ IsFppfTorsor G q

namespace FreeQuot

universe u

variable {S : Scheme.{u}} {G X Y : Over S} [GrpObj G] [ModObj G X] {q : X ⟶ Y}

theorem IsFppfTorsor.existsUnique_smul (h : IsFppfTorsor G q) {T : Over S} (x y : T ⟶ X) (e : y ≫ q = x ≫ q) :
    ∃! g : T ⟶ G, g • x = y := by
  have h2 : h.1.lift y x e ≫ snd G X = x := h.1.lift_snd _ _ _
  refine ⟨h.1.lift y x e ≫ fst G X, ?_, fun g hg => ?_⟩
  · have : lift (h.1.lift y x e ≫ fst G X) x = h.1.lift y x e := by
      ext
      · simp
      · simp [h2]
    beta_reduce
    rw [Hom.smul_def, this, h.1.lift_fst]
  · have : lift g x = h.1.lift y x e := by
      apply h.1.hom_ext
      · rw [h.1.lift_fst]; exact hg
      · rw [h.1.lift_snd, lift_snd]
    rw [← this, lift_fst]

set_option backward.isDefEq.respectTransparency.types false in

theorem IsFppfTorsor.of_descendsAlong (h : IsFppfTorsor G q) (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] (hG : P G.hom) : P q.left := by
  obtain ⟨hp, J, U, f, hf, hs, hl⟩ := h
  choose s hl using hl
  have hp' : IsPullback (γ[G, X] : G ⊗ X ⟶ X).left (snd G X).left q.left q.left := hp.map (Over.forget S)
  have h1 : P (snd G X).left := MorphismProperty.pullback_snd (P := P) G.hom X.hom hG
  have e : Sigma.desc s ≫ q.left = Sigma.desc f := by
    ext i; simp [hl]
  have hq := (IsPullback.of_hasPullback (snd G X).left (Sigma.desc s)).flip.paste_vert hp'.flip
  rw [e] at hq
  have := fun i => (hf i).1
  have := fun i => (hf i).2
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := P)
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hq ⟨⟨⟨fun y => ?_⟩, ?_⟩, ?_⟩
    (MorphismProperty.pullback_snd _ _ h1)
  · obtain ⟨i, z, rfl⟩ := hs y
    exact ⟨Sigma.ι U i z, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]⟩
  · exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance
  · exact IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance

theorem IsFppfTorsor.surjective (h : IsFppfTorsor G q) : Surjective q.left := by
  obtain ⟨-, J, U, f, -, hs, hl⟩ := h
  refine ⟨fun y => ?_⟩
  obtain ⟨i, z, rfl⟩ := hs y
  obtain ⟨s, e⟩ := hl i
  exact ⟨s z, by rw [← Scheme.Hom.comp_apply, e]⟩

set_option backward.isDefEq.respectTransparency.types false in

theorem IsFppfTorsor.isFiniteLocallyFree {S : Scheme.{0}} {G X Y : Over S} [GrpObj G] [ModObj G X] {q : X ⟶ Y}
    (h : IsFppfTorsor G q) (hG : IsFiniteLocallyFree G.hom) : IsFiniteLocallyFree q.left := by
  obtain ⟨h1, h2, h3⟩ := hG
  have := isAffineHom_descendsAlong_fpqc.{0}
  have := flat_descendsAlong_fpqc
  have a2 : IsAffineHom q.left := h.of_descendsAlong @IsAffineHom (inferInstanceAs (IsAffineHom G.hom))
  have a3 : UniversallyClosed q.left :=
    h.of_descendsAlong @UniversallyClosed (inferInstanceAs (UniversallyClosed G.hom))
  have a4 : LocallyOfFinitePresentation q.left := h.of_descendsAlong @LocallyOfFinitePresentation h3
  exact ⟨(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, inferInstance⟩,
    h.of_descendsAlong @Flat h2, a4⟩

theorem IsFppfTorsor.isFppfQuotient (h : IsFppfTorsor G q) : IsFppfQuotient G q := by
  refine ⟨h.1.w, ?_, ?_⟩
  · refine Presheaf.isLocallyInjective_of_injective _ _ ?_
    rintro T ⟨x⟩ ⟨y⟩ e
    obtain ⟨g, hg, -⟩ := h.existsUnique_smul y x e
    exact Quotient.sound ⟨g, hg⟩
  · obtain ⟨hp, J, U, f, hf, hs, hl⟩ := h
    refine ⟨fun {T} y => ?_⟩
    have hc : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage Y.left :=
      (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨hs, hf⟩
    have := Scheme.fppfTopology.pullback_stable y.left (Precoverage.generate_mem_toGrothendieck hc)
    rw [GrothendieckTopology.mem_over_iff]
    refine Scheme.fppfTopology.superset_covering ?_ this
    rintro V a ⟨W, b, c, ⟨i⟩, e⟩
    obtain ⟨s, hs⟩ := hl i
    rw [Sieve.overEquiv_iff]
    have e' : (b ≫ s) ≫ q.left = a ≫ y.left := by rw [Category.assoc, hs, e]
    refine ⟨Quotient.mk _ (Over.homMk (b ≫ s) ?_), ?_⟩
    · rw [← Over.w q, ← Category.assoc, e', Category.assoc, Over.w y]; rfl
    · exact Over.OverMorphism.ext e'

section Regular

attribute [local instance] ModObj.regular

end Regular

end FreeQuot

end GlobalTheory.CompanionTheory.Hypotheses₂
