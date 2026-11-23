import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsProperCurveThroughPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverIffLocallyOfFiniteTypeAndExistsIsAmpl
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite

open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.NormalCompletion

theorem exists_open_in_proper {R A : Type} [CommRing R] [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
    {Y : Scheme.{0}} (s : Y ⟶ Sp R) [IsProper s] (a : Sp A ⟶ Y) (h : a ≫ s = spMap (algebraMap R A)) :
    ∃ (X : Scheme.{0}) (u : Sp A ⟶ X) (c : X ⟶ Y), IsOpenImmersion u ∧ IsProper c ∧ u ≫ c = a := by
  have : LocallyOfFiniteType (spMap (algebraMap R A)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 ‹_›)
  obtain ⟨N, e, he, hq, hs⟩ := GlobalTheory.isQProjOver_comp_of_isAffineHom (spMap (algebraMap R A))
    (GlobalTheory.ZM.OnePoint.isQProjOver_id R)
  rw [Category.comp_id] at hs
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  let f : Sp A ⟶ pullback (PSpace.str R N) s := pullback.lift e a (hs.trans h.symm)
  have hf₁ : f ≫ pullback.fst _ _ = e := pullback.lift_fst _ _ _
  have hf₂ : f ≫ pullback.snd _ _ = a := pullback.lift_snd _ _ _
  have : IsImmersion (f ≫ pullback.fst _ _) := hf₁ ▸ he
  have : QuasiCompact (f ≫ pullback.fst _ _) := hf₁ ▸ hq
  have : IsImmersion f := .of_comp f (pullback.fst _ _)
  have : QuasiCompact f := .of_comp f (pullback.fst _ _)
  refine ⟨f.image, f.toImage, f.imageι ≫ pullback.snd _ _, inferInstance, inferInstance, ?_⟩
  rw [f.toImage_imageι_assoc, hf₂]

theorem exists_normal_proper : ∀ (k₀ k : Type) [Field k₀] [IsAlgClosed k₀] [Field k] (A : Type) [CommRing A] [Algebra k₀ A] (j : A →+* k) (Y : Scheme.{0}) (s : Y ⟶ Sp k₀) (a : Sp A ⟶ Y), Algebra.FiniteType k₀ A → Function.Injective j → IsProper s → a ≫ s = spMap (algebraMap k₀ A) → ∃ (W U : Scheme.{0}) (i : U ⟶ W) (π : U ⟶ Sp A) (b : W ⟶ Y) (w : Sp k ⟶ U), IsIntegral W ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme W ∧ IsProper (b ≫ s) ∧ IsOpenImmersion i ∧ i ≫ b = π ≫ a ∧ w ≫ π = spMap j := by
  intro k₀ k _ _ _ A _ _ j Y s a _ hj _ h
  have : IsDomain A := hj.isDomain j
  obtain ⟨X, u, c, _, _, huc⟩ := exists_open_in_proper s a h
  let K := FractionRing A
  let η : Sp K ⟶ Sp A := spMap (algebraMap A K)
  have : IsPreimmersion η := IsPreimmersion.of_isLocalization (R := A) (S := K) (nonZeroDivisors A)
  let g : Sp K ⟶ X := η ≫ u
  have : QuasiCompact g := QuasiCompact.of_comp g (c ≫ s)
  have : QuasiSeparated g := QuasiSeparated.of_comp g (c ≫ s)
  have : IsFinite g.fromNormalization := NormCurve.isFinite_fromNormalization g (c ≫ s)
  have hη : spMap (IsFractionRing.lift hj : K →+* k) ≫ η = spMap j := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact IsFractionRing.lift_algebraMap hj x
  refine ⟨g.normalization, pullback g.fromNormalization u, pullback.fst _ _, pullback.snd _ _,
    g.fromNormalization ≫ c,
    spMap (IsFractionRing.lift hj : K →+* k) ≫ pullback.lift g.toNormalization η g.toNormalization_fromNormalization,
    inferInstance, GlobalTheory.IsNormalScheme.pred _, inferInstance, inferInstance, ?_, ?_⟩
  · rw [pullback.condition_assoc, huc]
  · rw [Category.assoc, pullback.lift_snd, hη]

end GlobalTheory.NormalCompletion
