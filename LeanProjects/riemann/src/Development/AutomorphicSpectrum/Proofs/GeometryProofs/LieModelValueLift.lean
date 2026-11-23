import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.LieTangent

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp

theorem centre_field_base {K K' : Type} [Field K] [Field K'] {X : Scheme.{0}} (φ : K →+* K')
    (z : Sp K ⟶ X) : centre (Spec.map (CommRingCat.ofHom φ) ≫ z) = centre z := by
  have : Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K') = IsLocalRing.closedPoint K :=
    Subsingleton.elim _ _
  change (Spec.map (CommRingCat.ofHom φ) ≫ z) _ = z _
  rw [Scheme.Hom.comp_apply, this]

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem extends_generise (M : LieModel G ξ E) (p : Cpt ξ) {y : X} (hy : genPt ξ ⤳ y) (c : y ⤳ p.1) {e : E}
    {v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G} (h : M.Extends p e v) :
    M.Extends ⟨y, hy⟩ e (epsBase (R := X.presheaf.stalk p.1) (R' := X.presheaf.stalk y)
      (X.presheaf.stalkSpecializes c).hom (Scheme.SpecMap_stalkSpecializes_fromSpecStalk c) ≫ v) := by
  rw [LieModel.extends_iff] at *
  refine ⟨isTanAt_base _ _ h.1, ?_⟩
  rw [h.2, ← Category.assoc]
  congr 1
  refine Over.OverMorphism.ext ?_
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [spec_comp, ← dualMap_comp]
  congr 3
  exact RingHom.ext fun s => (genMap_specializes p hy c s).symm

theorem valAt_lie_base {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R')
    (M : LieModel G ξ E) {z : Sp R ⟶ X} {z' : Sp R' ⟶ X} (hz : Spec.map (CommRingCat.ofHom φ) ≫ z = z')
    (hg : genPt ξ ⤳ centre z') {e : E} {w : epsAt z ⟶ G} (h : M.ValAt z e w) :
    M.ValAt z' e (epsBase φ hz ≫ w) := by
  subst hz
  rw [LieModel.valAt_iff] at *
  obtain ⟨h1, v, hv, rfl⟩ := h
  refine ⟨hg, _, extends_generise M ⟨centre z, h1⟩ hg (centre_specializes φ z) hv, ?_⟩
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  refine Over.OverMorphism.ext ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [spec_comp, spec_comp, ← dualMap_comp, ← dualMap_comp]
  congr 3
  exact congrArg (fun g => g.hom) (stalk_base φ z).symm

end

theorem pull_lie_value : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (Bc : Type) [AddCommGroup Bc] [Module (𝓞 L) Bc] (MB : LieModel G z Bc) (x : Bc) (e : Li)
    (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
    M.ValAt _ e v → MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x v →
    ∃ v' : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G, M.ValAt _ e v' ∧
      MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) x v' := by
  intro X Ω _ ξ G _ Li _ _ M L _ _ z σ Bc _ _ MB x e v hv hl
  have hz : Spec.map (CommRingCat.ofHom σ) ≫ (spMap (algebraMap (𝓞 L) L) ≫ z) =
      spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z := by
    rw [← Category.assoc, spec_comp]
  have hg : genPt ξ ⤳ centre (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) := by
    obtain ⟨h1, -⟩ := hv
    rw [← hz, centre_field_base]
    exact h1
  refine ⟨epsBase σ hz ≫ v, valAt_lie_base σ M hz hg hv, ?_⟩
  unfold LieModel.Lifts at *
  change (Spec.map _ ≫ v.left) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rw [Category.comp_id] at hl
  rw [hl, ← Category.assoc, spec_comp, ← dualMap_comp]

end GlobalTheory.CompanionTheory.Ar.RootHt
