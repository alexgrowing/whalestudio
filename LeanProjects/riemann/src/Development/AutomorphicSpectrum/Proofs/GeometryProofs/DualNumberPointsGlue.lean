import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DualMapSOfIdToRingHom

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Chart (dAway dAway_ext dAway_lift isUnit_dAway Ld toL fromL toL_comp fromL_comp fromL_toL)

namespace GlobalTheory.CompanionTheory.Ar.LieFinGlue

variable {R : Type} [CommRing R]

theorem dualMap_algebraMap_eq_dAway (s : R) : dualMap (algebraMap R (Localization.Away s)) = dAway s := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]

theorem dualMap_comp_dualMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (p : B →+* C) (q : A →+* B) :
    (dualMap p).comp (dualMap q) = dualMap (p.comp q) := by
  refine RingHom.ext fun x => ?_
  ext <;> simp [dualMap]

theorem span_range_inl {J : Type} (f : J → R) (hf : Ideal.span (Set.range f) = ⊤) :
    Ideal.span (Set.range fun k => (TrivSqZeroExt.inl (f k) : DualNumber R)) = ⊤ := by
  have := congrArg (Ideal.map (TrivSqZeroExt.inlHom R R)) hf
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  exact this

theorem spMap_algebraMap_eq (s : R) :
    spMap (algebraMap (DualNumber R) (Ld s)) = spMap (toL s) ≫ spMap (dAway s) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toL_comp]

theorem sep_base {X : Scheme.{0}} {J : Type} (f : J → R) (hf : Ideal.span (Set.range f) = ⊤)
    (a b : Sp R ⟶ X)
    (h : ∀ i, spMap (algebraMap R (Localization.Away (f i))) ≫ a =
      spMap (algebraMap R (Localization.Away (f i))) ≫ b) : a = b :=
  Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of R) _ hf).openCover _ _
    fun (k : J) => h k

theorem sep_dual {X : Scheme.{0}} {J : Type} (f : J → R) (hf : Ideal.span (Set.range f) = ⊤)
    (a b : Sp (DualNumber R) ⟶ X)
    (h : ∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ a =
      spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ b) : a = b := by
  refine Scheme.Cover.hom_ext
    (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber R)) _ (span_range_inl f hf)).openCover
    _ _ fun (k : J) => ?_
  have hk := h k
  rw [dualMap_algebraMap_eq_dAway] at hk
  show spMap (algebraMap (DualNumber R) (Ld (f k))) ≫ a = spMap (algebraMap (DualNumber R) (Ld (f k))) ≫ b
  rw [spMap_algebraMap_eq, Category.assoc, Category.assoc, hk]

theorem compat_of_pair {X : Scheme.{0}} {J : Type} (f : J → R)
    (w : ∀ i, Sp (DualNumber (Localization.Away (f i))) ⟶ X)
    (hw : ∀ i j (a : Localization.Away (f i) →+* Localization.Away (f i * f j))
      (b : Localization.Away (f j) →+* Localization.Away (f i * f j)),
      a.comp (algebraMap R _) = algebraMap R _ → b.comp (algebraMap R _) = algebraMap R _ →
      spMap (dualMap a) ≫ w i = spMap (dualMap b) ≫ w j)
    (i j : J) (T : CommRingCat.{0}) (α : DualNumber (Localization.Away (f i)) →+* T)
    (β : DualNumber (Localization.Away (f j)) →+* T) (h : α.comp (dAway (f i)) = β.comp (dAway (f j))) :
    Spec.map (CommRingCat.ofHom α) ≫ w i = Spec.map (CommRingCat.ofHom β) ≫ w j := by
  have hi : IsUnit ((α.comp (dAway (f i))) (TrivSqZeroExt.inl (f i))) := (isUnit_dAway (f i)).map α
  have hj : IsUnit ((α.comp (dAway (f i))) (TrivSqZeroExt.inl (f j))) := by
    rw [h]
    exact (isUnit_dAway (f j)).map β
  have hij : IsUnit ((α.comp (dAway (f i))) (TrivSqZeroExt.inl (f i * f j))) := by
    rw [TrivSqZeroExt.inl_mul, map_mul]
    exact hi.mul hj
  obtain ⟨χ, hχ⟩ := dAway_lift (f i * f j) (α.comp (dAway (f i))) hij
  have hu : IsUnit (algebraMap R (Localization.Away (f i * f j)) (f i * f j)) :=
    IsLocalization.Away.algebraMap_isUnit (f i * f j)
  rw [map_mul] at hu
  have ui : IsUnit (algebraMap R (Localization.Away (f i * f j)) (f i)) := isUnit_of_mul_isUnit_left hu
  have uj : IsUnit (algebraMap R (Localization.Away (f i * f j)) (f j)) := isUnit_of_mul_isUnit_right hu
  let a : Localization.Away (f i) →+* Localization.Away (f i * f j) := IsLocalization.Away.lift (f i) ui
  let b : Localization.Away (f j) →+* Localization.Away (f i * f j) := IsLocalization.Away.lift (f j) uj
  have ha : a.comp (algebraMap R _) = algebraMap R _ := IsLocalization.Away.lift_comp _ ui
  have hb : b.comp (algebraMap R _) = algebraMap R _ := IsLocalization.Away.lift_comp _ uj
  have hα : χ.comp (dualMap a) = α := dAway_ext (f i) (by
    rw [RingHom.comp_assoc, ← dualMap_algebraMap_eq_dAway (f i), dualMap_comp_dualMap, ha,
      dualMap_algebraMap_eq_dAway, hχ, dualMap_algebraMap_eq_dAway])
  have hβ : χ.comp (dualMap b) = β := dAway_ext (f j) (by
    rw [RingHom.comp_assoc, ← dualMap_algebraMap_eq_dAway (f j), dualMap_comp_dualMap, hb,
      dualMap_algebraMap_eq_dAway, hχ, dualMap_algebraMap_eq_dAway, h])
  have e := hw i j a b ha hb
  rw [← hα, ← hβ, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc,
    Category.assoc]
  exact congrArg (Spec.map (CommRingCat.ofHom χ) ≫ ·) e

set_option backward.isDefEq.respectTransparency false in

theorem glue_of_compat {X : Scheme.{0}} {J : Type} (f : J → R) (hf : Ideal.span (Set.range f) = ⊤)
    (w : ∀ i, Sp (DualNumber (Localization.Away (f i))) ⟶ X)
    (hc : ∀ k l (T : CommRingCat.{0}) (α : DualNumber (Localization.Away (f k)) →+* T)
      (β : DualNumber (Localization.Away (f l)) →+* T), α.comp (dAway (f k)) = β.comp (dAway (f l)) →
      Spec.map (CommRingCat.ofHom α) ≫ w k = Spec.map (CommRingCat.ofHom β) ≫ w l) :
    ∃ v : Sp (DualNumber R) ⟶ X, ∀ i, spMap (dAway (f i)) ≫ v = w i := by
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber R)) _
    (span_range_inl f hf)).openCover
  let g : ∀ k, 𝒰.X k ⟶ X := fun k => Spec.map (CommRingCat.ofHom (toL (f k))) ≫ w k
  have hg : ∀ k l, pullback.fst (𝒰.f k) (𝒰.f l) ≫ g k = pullback.snd (𝒰.f k) (𝒰.f l) ≫ g l := by
    refine fun (k : J) (l : J) => Scheme.Cover.hom_ext (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.openCover _ _
      fun (i : (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.I₀) => ?_
    let a : Spec ((pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i) ⟶ pullback (𝒰.f k) (𝒰.f l) :=
      (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.f i
    let A : CommRingCat.of (Ld (f k)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.fst (𝒰.f k) (𝒰.f l))
    let B : CommRingCat.of (Ld (f l)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.snd (𝒰.f k) (𝒰.f l))
    have ea : Spec.map A = a ≫ pullback.fst (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have eb : Spec.map B = a ≫ pullback.snd (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap (DualNumber R) (Ld (f k))) ≫ A) =
        Spec.map (CommRingCat.ofHom (algebraMap (DualNumber R) (Ld (f l))) ≫ B) := by
      rw [Spec.map_comp, Spec.map_comp, ea, eb, Category.assoc, Category.assoc]
      exact congrArg (a ≫ ·) pullback.condition
    have key : A.hom.comp (algebraMap (DualNumber R) (Ld (f k))) =
        B.hom.comp (algebraMap (DualNumber R) (Ld (f l))) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    have hkey : (A.hom.comp (toL (f k))).comp (dAway (f k)) = (B.hom.comp (toL (f l))).comp (dAway (f l)) := by
      rw [RingHom.comp_assoc, RingHom.comp_assoc, toL_comp, toL_comp]
      exact key
    have h := hc k l _ (A.hom.comp (toL (f k))) (B.hom.comp (toL (f l))) hkey
    show a ≫ pullback.fst (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (f k))) ≫ w k =
      a ≫ pullback.snd (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (toL (f l))) ≫ w l
    rw [← Category.assoc a, ← Category.assoc a, ← ea, ← eb, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp]
    exact h
  refine ⟨𝒰.glueMorphisms g hg, fun k => ?_⟩
  have hι : 𝒰.f k ≫ 𝒰.glueMorphisms g hg = g k := Scheme.Cover.ι_glueMorphisms 𝒰 g hg k
  have e : spMap (dAway (f k)) = Spec.map (CommRingCat.ofHom (fromL (f k))) ≫ 𝒰.f k := by
    show _ = _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (DualNumber R) (Ld (f k))))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_comp]
  rw [e, Category.assoc, hι]
  show Spec.map (CommRingCat.ofHom (fromL (f k))) ≫ Spec.map (CommRingCat.ofHom (toL (f k))) ≫ w k = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fromL_toL, CommRingCat.ofHom_id, Spec.map_id,
    Category.id_comp]

theorem dual_glue : ∀ (X : Scheme.{0}) (R : Type) [CommRing R] (J : Type) [Finite J] (f : J → R),
    Ideal.span (Set.range f) = ⊤ →
  (∀ a b : Sp R ⟶ X, (∀ i, spMap (algebraMap R (Localization.Away (f i))) ≫ a = spMap (algebraMap R (Localization.Away (f i))) ≫ b) → a = b) ∧
  (∀ a b : Sp (DualNumber R) ⟶ X,
    (∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ a = spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ b) → a = b) ∧
  ∀ w : ∀ i, Sp (DualNumber (Localization.Away (f i))) ⟶ X,
    (∀ i j (a : Localization.Away (f i) →+* Localization.Away (f i * f j)) (b : Localization.Away (f j) →+* Localization.Away (f i * f j)),
      a.comp (algebraMap R _) = algebraMap R _ → b.comp (algebraMap R _) = algebraMap R _ →
      spMap (dualMap a) ≫ w i = spMap (dualMap b) ≫ w j) →
    ∃ v : Sp (DualNumber R) ⟶ X, ∀ i, spMap (dualMap (algebraMap R (Localization.Away (f i)))) ≫ v = w i := by
  intro X R _ J _ f hf
  refine ⟨sep_base f hf, sep_dual f hf, fun w hw => ?_⟩
  obtain ⟨v, hv⟩ := glue_of_compat f hf w (compat_of_pair f w hw)
  exact ⟨v, fun i => by rw [dualMap_algebraMap_eq_dAway]; exact hv i⟩

end GlobalTheory.CompanionTheory.Ar.LieFinGlue
