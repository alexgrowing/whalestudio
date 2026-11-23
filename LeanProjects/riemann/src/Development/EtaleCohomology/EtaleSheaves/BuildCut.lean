import Development.EtaleCohomology.EtaleSheaves.CoverCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.CoverCut

namespace LateralTheory.E.BuildCut

def ProdACF (W : Type) [CommRing W] : Prop :=
  AIC W ∧ ∀ a : W, ∃ e u : W, IsIdempotentElem e ∧ IsUnit u ∧ a = e * u

def Pts : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P],
  ∃ (W : Type) (_ : CommRing W) (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W ∧ Surjective w

def LimInt : Prop := ∀ {Y : Scheme.{0}} (y : Y) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D)
  (ι : ∀ j, D.obj j ⟶ Y), ClopenSys y D c ι → ∀ j, IsIntegralHom (c.π.app j ≫ ι j)

def Comp : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P] (W : Type) [CommRing W]
  (w : Spec (CommRingCat.of W) ⟶ P), ProdACF W → ∀ y : w.normalization,
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ w.normalization),
      ClopenSys y D c ι ∧ AICSch c.pt

theorem goal_of (hP : Pts) (hL : LimInt) (hC : Comp) : Build := by
  intro P _ _
  obtain ⟨W, _, w, hW, hs⟩ := hP (P := P)
  refine ⟨w.normalization, w.fromNormalization, inferInstance, ?_, fun y => ?_⟩
  · have h := hs
    rw [← w.toNormalization_fromNormalization] at h
    exact ⟨Function.Surjective.of_comp h.surj⟩
  · obtain ⟨J, _, _, D, c, ι, hc, hA⟩ := hC W w hW y
    refine ⟨J, inferInstance, inferInstance, D, c, ι, hc, hA, fun j => ?_⟩
    have := hL y D c ι hc j
    infer_instance

end LateralTheory.E.BuildCut
