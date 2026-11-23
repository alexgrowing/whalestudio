import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelComplexBaseChange
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtComplexEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieSigma.ValBC

open GlobalTheory.CompanionTheory.Ar.RootHt.PullVal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem dualMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : B →+* C) (f : A →+* B) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;> simp [dualMap]

theorem stalk_key {K K' : Type} [Field K] [Field K'] (w : Spec (CommRingCat.of K) ⟶ X)
    (w' : Spec (CommRingCat.of K') ⟶ X) (f : K →+* K') (e : Spec.map (CommRingCat.ofHom f) ≫ w = w') :
    ∃ hc : centre w' = centre w, X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫
      Scheme.stalkClosedPointTo w' = Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f := by
  have hl : IsLocalHom (Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f).hom := by
    refine ⟨fun b hb => ?_⟩
    have h1 : IsUnit (f ((Scheme.stalkClosedPointTo w).hom b)) := hb
    have h2 : IsUnit ((Scheme.stalkClosedPointTo w).hom b : K) :=
      isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at h1
    exact isUnit_of_map_unit (Scheme.stalkClosedPointTo w).hom b h2
  have e2 : w' = Spec.map (Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f) ≫
      X.fromSpecStalk (w (IsLocalRing.closedPoint (CommRingCat.of K))) := by
    rw [← e, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hc0 : (Spec.map (Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f) ≫
      X.fromSpecStalk (w (IsLocalRing.closedPoint (CommRingCat.of K))))
        (IsLocalRing.closedPoint (CommRingCat.of K')) =
      w (IsLocalRing.closedPoint (CommRingCat.of K)) :=
    closedPoint_specMap_fromSpecStalk (R := CommRingCat.of K') _ _
  have key0 := stalkSpecializes_stalkClosedPointTo _ _ hc0
  clear e
  subst e2
  exact ⟨hc0, key0⟩

variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem extends_of_eq (M : LieModel G ξ E) {c c' : X} (hc : c' = c) (h : genPt ξ ⤳ c) (a : E)
    (v : epsAt (R := X.presheaf.stalk c) (X.fromSpecStalk c) ⟶ G) (hv : M.Extends ⟨c, h⟩ a v)
    {K : Type} [CommRing K] (φ : X.presheaf.stalk c' ⟶ CommRingCat.of K) :
    ∃ (h' : genPt ξ ⤳ c') (v' : epsAt (R := X.presheaf.stalk c') (X.fromSpecStalk c') ⟶ G),
      M.Extends ⟨c', h'⟩ a v' ∧
      Spec.map (CommRingCat.ofHom (dualMap φ.hom)) ≫ v'.left =
        Spec.map (CommRingCat.ofHom (dualMap (X.presheaf.stalkSpecializes (specializes_of_eq hc) ≫ φ).hom)) ≫
          v.left := by
  subst hc
  refine ⟨h, v, hv, ?_⟩
  rw [TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]

theorem valAt_field_map : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (K K' : Type) [Field K] [Field K'] (w : Sp K ⟶ X) (f : K →+* K') (a : Li) (v : epsAt w ⟶ G), M.ValAt w a v → M.ValAt (spMap f ≫ w) a (GlobalTheory.CompanionTheory.Ar.LieSigma.pullEps f w ≫ v) := by
  intro X Ω _ ξ G _ Li _ _ M K K' _ _ w f a v hv
  obtain ⟨h, v₀, hE, hl⟩ := hv
  obtain ⟨hc, key⟩ := stalk_key w (spMap f ≫ w) f rfl
  obtain ⟨h', v', hE', hl'⟩ := extends_of_eq M hc h a v₀ hE (Scheme.stalkClosedPointTo (spMap f ≫ w))
  refine ⟨h', v', hE', ?_⟩
  refine Eq.trans ?_ hl'.symm
  rw [key, Over.comp_left, hl]
  simp only [GlobalTheory.CompanionTheory.Ar.LieSigma.pullEps, Over.homMk_left]
  have e1 : spMap (dualMap f) ≫ Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo w).hom)) =
      Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo w ≫ CommRingCat.ofHom f).hom)) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← dualMap_comp']
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ v₀.left) e1)

end GlobalTheory.CompanionTheory.Ar.LieSigma.ValBC
