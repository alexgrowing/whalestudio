import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.CoverCut

def ClopenSys {Y : Scheme.{0}} (y : Y) {J : Type} [SmallCategory J] (D : J ⥤ Scheme.{0}) (c : Cone D)
    (ι : ∀ j, D.obj j ⟶ Y) : Prop :=
  Nonempty (IsLimit c) ∧ (∀ j, IsOpenImmersion (ι j) ∧ IsClosedImmersion (ι j) ∧ y ∈ Set.range (ι j)) ∧
    ∀ {j k : J} (f : j ⟶ k), D.map f ≫ ι k = ι j ∧ IsAffineHom (D.map f)

def Build : Prop := ∀ {P : Scheme.{0}} [CompactSpace P] [QuasiSeparatedSpace P],
  ∃ (Y : Scheme.{0}) (k : Y ⟶ P), IsIntegralHom k ∧ Surjective k ∧
    ∀ y : Y, ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
      ClopenSys y D c ι ∧ AICSch c.pt ∧ ∀ j, IsIntegralHom ((c.π.app j ≫ ι j) ≫ k)

def ProEqv : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) →
  ∀ {Y : Scheme.{0}} [CompactSpace Y] [QuasiSeparatedSpace Y] (g : Y ⟶ Spec (CommRingCat.of A)),
  (∀ y : Y, ∃ (J : Type) (_ : SmallCategory J) (_ : IsCofiltered J) (D : J ⥤ Scheme.{0}) (c : Cone D) (ι : ∀ j, D.obj j ⟶ Y),
      ClopenSys y D c ι ∧ ∀ j, PB q i ((c.π.app j ≫ ι j) ≫ g)) →
  PB q i g

theorem goal_of (hB : Build) (hP : ProEqv) : Cover := by
  intro H q i A _ _ hq P _ _ p hZ
  obtain ⟨Y, k, hk, hs, hY⟩ := hB (P := P)
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace k
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated k
  refine ⟨Y, k, hk, hs, hP H q i A hq (k ≫ p) fun y => ?_⟩
  obtain ⟨J, _, _, D, c, ι, hc, hA, hint⟩ := hY y
  refine ⟨J, inferInstance, inferInstance, D, c, ι, hc, fun j => ?_⟩
  have := hZ c.pt ((c.π.app j ≫ ι j) ≫ k) (hint j) hA
  simpa only [Category.assoc] using this

end LateralTheory.E.CoverCut
