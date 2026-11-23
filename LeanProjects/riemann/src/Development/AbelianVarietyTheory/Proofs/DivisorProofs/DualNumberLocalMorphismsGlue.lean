import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DualMapSOfIdToRingHom
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GlueTanAway

open Limits

variable {L : Type} [CommRing L]

theorem dualMap_algebraMap_eq (a : L) :
    Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away a)) = Chart.dAway a :=
  RingHom.ext fun x => TrivSqZeroExt.ext (by simp [Formalism.L2.Pj.dualMap, Chart.dualMapR])
    (by simp [Formalism.L2.Pj.dualMap, Chart.dualMapR])

theorem dualMap_comp_dAway (a : L) (c : L)
    (φ : Localization.Away a →+* Localization.Away c) (hφ : ∀ x, φ (algebraMap L _ x) = algebraMap L (Localization.Away c) x) :
    (Formalism.L2.Pj.dualMap φ).comp (Chart.dAway a) = (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away c))) := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  all_goals simp only [RingHom.comp_apply, Formalism.L2.Pj.dualMap, Chart.dualMapR, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, add_zero, zero_add, hφ]

theorem factor_ab (a b : L) {T : Type} [CommRing T] (α : DualNumber (Localization.Away a) →+* T)
    (β : DualNumber (Localization.Away b) →+* T) (h : α.comp (Chart.dAway a) = β.comp (Chart.dAway b)) :
    ∃ γ : DualNumber (Localization.Away (a * b)) →+* T,
      α = γ.comp (Formalism.L2.Pj.dualMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away a)
        (P := Localization.Away (a * b)) a b)) ∧
      β = γ.comp (Formalism.L2.Pj.dualMap (IsLocalization.Away.awayToAwayLeft (S := Localization.Away b)
        (P := Localization.Away (a * b)) b a)) := by
  have hu : IsUnit ((α.comp (Chart.dAway a)) (TrivSqZeroExt.inl (a * b))) := by
    rw [← TrivSqZeroExt.inl_mul_inl, map_mul]
    refine ((Chart.isUnit_dAway a).map α).mul ?_
    rw [h]
    exact (Chart.isUnit_dAway b).map β
  obtain ⟨γ, hγ⟩ := Chart.dAway_lift (a * b) (α.comp (Chart.dAway a)) hu
  have eγ : γ.comp (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a * b)))) = α.comp (Chart.dAway a) := by
    rw [dualMap_algebraMap_eq]; exact hγ
  refine ⟨γ, Chart.dAway_ext a ?_, Chart.dAway_ext b ?_⟩
  · rw [RingHom.comp_assoc, dualMap_comp_dAway a (a * b) _ (fun x => IsLocalization.Away.awayToAwayRight_eq a b x), eγ]
  · rw [RingHom.comp_assoc, dualMap_comp_dAway b (a * b) _ (fun x => IsLocalization.Away.awayToAwayLeft_eq b a x), eγ, h]

end GlobalTheory.GlueTanAway

namespace GlobalTheory.GlueTanAway

open Limits

set_option backward.isDefEq.respectTransparency false in

theorem glue_away_dual : ∀ {L : Type} [CommRing L] {s : Set L}, Ideal.span s = ⊤ → ∀ {Y : Scheme.{0}} (w : ∀ a : s, Sp (DualNumber (Localization.Away (a : L))) ⟶ Y), (∀ a b : s, spMap (Formalism.L2.Pj.dualMap (IsLocalization.Away.awayToAwayRight (S := Localization.Away (a : L)) (P := Localization.Away ((a : L) * b)) (a : L) (b : L))) ≫ w a = spMap (Formalism.L2.Pj.dualMap (IsLocalization.Away.awayToAwayLeft (S := Localization.Away (b : L)) (P := Localization.Away ((a : L) * b)) (b : L) (a : L))) ≫ w b) → ∃ w₀ : Sp (DualNumber L) ⟶ Y, ∀ a : s, spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (a : L)))) ≫ w₀ = w a := by
  intro L _ s hs Y w hw
  have hs' : Ideal.span (Set.range (fun a : s => (TrivSqZeroExt.inl (a : L) : DualNumber L))) = ⊤ := by
    have := congrArg (Ideal.map (TrivSqZeroExt.inlHom L L)) hs
    rw [Ideal.map_span, Ideal.map_top] at this
    rw [← this]
    congr 1
    ext x
    simp
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of (DualNumber L)) _ hs').openCover
  let f : ∀ k : s, 𝒰.X k ⟶ Y := fun k => Spec.map (CommRingCat.ofHom (Chart.toL (k : L))) ≫ w k
  have hf : ∀ k l, pullback.fst (𝒰.f k) (𝒰.f l) ≫ f k = pullback.snd (𝒰.f k) (𝒰.f l) ≫ f l := by
    refine fun (k : s) (l : s) => Scheme.Cover.hom_ext (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.openCover _ _
      fun (i : (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.I₀) => ?_
    let a : Spec ((pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i) ⟶ pullback (𝒰.f k) (𝒰.f l) :=
      (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.f i
    let A : CommRingCat.of (Chart.Ld (k : L)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.fst (𝒰.f k) (𝒰.f l))
    let B : CommRingCat.of (Chart.Ld (l : L)) ⟶ (pullback (𝒰.f k) (𝒰.f l)).affineOpenCover.X i :=
      Spec.preimage (a ≫ pullback.snd (𝒰.f k) (𝒰.f l))
    have ea : Spec.map A = a ≫ pullback.fst (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have eb : Spec.map B = a ≫ pullback.snd (𝒰.f k) (𝒰.f l) := Spec.map_preimage _
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap (DualNumber L) (Chart.Ld (k : L))) ≫ A) =
        Spec.map (CommRingCat.ofHom (algebraMap (DualNumber L) (Chart.Ld (l : L))) ≫ B) := by
      rw [Spec.map_comp, Spec.map_comp, ea, eb, Category.assoc, Category.assoc]
      exact congrArg (a ≫ ·) pullback.condition
    have key : A.hom.comp (algebraMap (DualNumber L) (Chart.Ld (k : L))) =
        B.hom.comp (algebraMap (DualNumber L) (Chart.Ld (l : L))) :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e1)
    have hkey : (A.hom.comp (Chart.toL (k : L))).comp (Chart.dAway (k : L)) =
        (B.hom.comp (Chart.toL (l : L))).comp (Chart.dAway (l : L)) := by
      rw [RingHom.comp_assoc, RingHom.comp_assoc, Chart.toL_comp, Chart.toL_comp]
      exact key
    obtain ⟨γ, hα, hβ⟩ := factor_ab (k : L) (l : L) _ _ hkey
    have h : Spec.map (CommRingCat.ofHom (A.hom.comp (Chart.toL (k : L)))) ≫ w k =
        Spec.map (CommRingCat.ofHom (B.hom.comp (Chart.toL (l : L)))) ≫ w l := by
      rw [hα, hβ, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc,
        Category.assoc]
      exact congrArg (Spec.map (CommRingCat.ofHom γ) ≫ ·) (hw k l)
    show a ≫ pullback.fst (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (Chart.toL (k : L))) ≫ w k =
      a ≫ pullback.snd (𝒰.f k) (𝒰.f l) ≫ Spec.map (CommRingCat.ofHom (Chart.toL (l : L))) ≫ w l
    rw [← Category.assoc a, ← Category.assoc a, ← ea, ← eb, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp]
    exact h
  let g := 𝒰.glueMorphisms f hf
  have hι : ∀ k : s, 𝒰.f k ≫ g = f k := fun k => Scheme.Cover.ι_glueMorphisms 𝒰 f hf k
  refine ⟨g, fun k => ?_⟩
  have e : spMap (Formalism.L2.Pj.dualMap (algebraMap L (Localization.Away (k : L)))) =
      Spec.map (CommRingCat.ofHom (Chart.fromL (k : L))) ≫ 𝒰.f k := by
    rw [dualMap_algebraMap_eq]
    show _ = _ ≫ Spec.map (CommRingCat.ofHom (algebraMap (DualNumber L) (Chart.Ld (k : L))))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Chart.fromL_comp]
  rw [e, Category.assoc, hι k]
  show Spec.map (CommRingCat.ofHom (Chart.fromL (k : L))) ≫ Spec.map (CommRingCat.ofHom (Chart.toL (k : L))) ≫ w k = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Chart.fromL_toL, CommRingCat.ofHom_id, Spec.map_id,
    Category.id_comp]

end GlobalTheory.GlueTanAway
