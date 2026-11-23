import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConstStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ExtensionRigidity

theorem hom_ext_of_rationalPoints {K : Type} [Field K] [IsAlgClosed K] {X Y : Over (Sp K)}
    [Smooth X.hom] [IsProper Y.hom] (f g : X ⟶ Y)
    (h : ∀ x : 𝟙_ (Over (Sp K)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have := isNormalScheme_of_smooth (S := Spec (.of K)) X.hom
  have : IsReduced X.left := IsNormalScheme.isReduced
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  refine Over.OverMorphism.ext (ext_of_apply_eq (K := K) Y.hom Set.univ
    isOpen_univ.isLocallyClosed dense_univ (fun x _ hx => ?_) (by rw [Over.w, Over.w]))
  let p : 𝟙_ (Over (Sp K)) ⟶ X :=
    Over.homMk (pointOfClosedPoint (K := K) X.hom x hx) (pointOfClosedPoint_comp (K := K) X.hom x hx)
  have h1 : pointOfClosedPoint (K := K) X.hom x hx ≫ f.left =
      pointOfClosedPoint (K := K) X.hom x hx ≫ g.left := congrArg CommaMorphism.left (h p)
  have h2 : f.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) =
      g.left (pointOfClosedPoint (K := K) X.hom x hx (IsLocalRing.closedPoint K)) :=
    congrArg (fun φ => φ (IsLocalRing.closedPoint K)) h1
  have h3 := pointOfClosedPoint_apply (K := K) X.hom x hx (IsLocalRing.closedPoint K)
  exact (congrArg f.left h3).symm.trans (h2.trans (congrArg g.left h3))

theorem exists_factor {S : Scheme.{0}} {X Y Z : Over S} (p : X ⟶ Y) [Flat p.left]
    [Surjective p.left] [QuasiCompact p.left] (f : X ⟶ Z)
    (h : ∀ (W : Over S) (a b : W ⟶ X), a ≫ p = b ≫ p → a ≫ f = b ≫ f) :
    ∃ β : Y ⟶ Z, p ≫ β = f := by
  have hc : ∀ {W : Scheme.{0}} (g g' : W ⟶ X.left), g ≫ p.left = g' ≫ p.left →
      g ≫ f.left = g' ≫ f.left := by
    intro W g g' hg
    have hw : g' ≫ X.hom = g ≫ X.hom := by
      rw [← Over.w p, ← Category.assoc, ← hg, Category.assoc]
    have := h (Over.mk (g ≫ X.hom)) (Over.homMk g rfl) (Over.homMk g' hw)
      (Over.OverMorphism.ext hg)
    exact congrArg CommaMorphism.left this
  have hfac := EffectiveEpi.fac p.left f.left hc
  exact ⟨Over.homMk (EffectiveEpi.desc p.left f.left hc) (by
    rw [← cancel_epi p.left, ← Category.assoc, hfac, Over.w, Over.w]),
    Over.OverMorphism.ext hfac⟩

theorem isMonHom_of_pointed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : G ⟶ B, η[G] ≫ f = η[B] → IsMonHom f := by
  intro K _ _ E G _ hG B _ hB f hf
  have := (UnitRigidity.smooth_geometricallyConnected_of_isGt E G hG).1
  obtain ⟨D⟩ := hG
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have := hB.proper
  obtain ⟨-, -, -, -, h1, -⟩ := (splitTorus_properties (Sp K)).1 E.X
  have : Smooth (splitTorus (Sp K) E.X).hom :=
    SmoothOfRelativeDimension.smooth (Module.finrank ℤ E.X) _
  have : Smooth (splitTorus (Sp K) E.X ⊗ G).hom :=
    inferInstanceAs (Smooth (pullback.fst (splitTorus (Sp K) E.X).hom G.hom ≫
      (splitTorus (Sp K) E.X).hom))
  have hact : ((fst (splitTorus (Sp K) E.X) G ≫ D.i) * snd _ G) ≫ f = snd _ G ≫ f := by
    refine hom_ext_of_rationalPoints _ _ fun x => ?_
    obtain ⟨b, hb⟩ := GlobalTheory.T.splitTorus_to_abelianVariety_const K E.X B hB ((D.i * (toUnit _ ≫ x ≫ snd _ G)) ≫ f)
    have e : ∀ t : 𝟙_ (Over (Sp K)) ⟶ splitTorus (Sp K) E.X,
        ((t ≫ D.i) * (x ≫ snd _ G)) ≫ f = b := by
      intro t
      have := congrArg (t ≫ ·) hb
      simp only [← Category.assoc, MonObj.comp_mul] at this
      rw [toUnit_unique (t ≫ toUnit _) (𝟙 _), Category.id_comp, Category.id_comp] at this
      exact this
    have e1 := e 1
    rw [MonObj.one_comp, _root_.one_mul] at e1
    rw [← Category.assoc, MonObj.comp_mul, ← Category.assoc, e, ← Category.assoc, e1]
  obtain ⟨β, hβ⟩ := exists_factor D.q f fun W a c h => by
    have H := UnitRigidity.isPullback_act D.i D.q D.isKernel
    rw [← H.lift_fst a c h, Category.assoc, hact, ← Category.assoc, H.lift_snd]
  have : IsMonHom β := rigidity_holds _ _ _ E.isAbelian hB β (by
    rw [← IsMonHom.one_hom D.q, Category.assoc, hβ, hf])
  rw [← hβ]
  infer_instance

end GlobalTheory.ExtensionRigidity
