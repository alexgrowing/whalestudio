import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianPartBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackUniqueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductConjugateStatement
import Development.WeilBound.CoreStatements.AmpleLineBundles.IsPrincipalIffOfBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace PositivityTheory.Xgn.QuotientUniformizationConjugate

noncomputable def lf {S : Scheme.{0}} {G : Over S} {R : Type} [CommRing R] {x : Sp R ⟶ S} (v : epsAt x ⟶ G) :
    Sp (DualNumber R) ⟶ G.left :=
  v.left

theorem sq_alg {R R' : Type} [CommRing R] [CommRing R'] (e : R →+* R') :
    spMap (dualMap e) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R' (DualNumber R')) ≫ spMap e := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun r => ?_
  show dualMap e (algebraMap R (DualNumber R) r) = algebraMap R' (DualNumber R') (e r)
  rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl]
  ext <;> simp [dualMap]

theorem sq_fst {R R' : Type} [CommRing R] [CommRing R'] (e : R →+* R') :
    spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMap e) =
      spMap e ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun r => ?_
  show (dualMap e r).fst = e r.fst
  simp [dualMap]

theorem one_comp {S T T' : Scheme.{0}} (G : Over S) [GrpObj G] (x : T ⟶ S) (a : T' ⟶ T) :
    a ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (a ≫ x) ⟶ G).left := by
  let k : Over.mk (a ≫ x) ⟶ Over.mk x := Over.homMk a rfl
  have : k ≫ (1 : Over.mk x ⟶ G) = 1 := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]
  exact congrArg (fun q => q.left) this

theorem exists_bc {S : Scheme.{0}} {G : Over S} [GrpObj G] {R R' : Type} [CommRing R] [CommRing R'] (e : R →+* R')
    (z : Sp R ⟶ S) (z' : Sp R' ⟶ S) (hz : z' = spMap e ≫ z) (v : epsAt z ⟶ G) :
    ∃ v' : epsAt z' ⟶ G, lf v' = spMap (dualMap e) ≫ lf v ∧ (IsTanAt G z v → IsTanAt G z' v') := by
  subst hz
  have hw : lf v ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ z := Over.w v
  refine ⟨Over.homMk (spMap (dualMap e) ≫ lf v) ?_, rfl, fun ht => ?_⟩
  · show (spMap (dualMap e) ≫ lf v) ≫ G.hom = spMap (algebraMap R' (DualNumber R')) ≫ spMap e ≫ z
    rw [Category.assoc, hw, ← Category.assoc, sq_alg, Category.assoc]
  · have ht' : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ lf v = (1 : Over.mk z ⟶ G).left := ht
    show spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMap e) ≫ lf v =
      (1 : Over.mk (spMap e ≫ z) ⟶ G).left
    rw [← Category.assoc, sq_fst, Category.assoc, ht']
    exact one_comp G z (spMap e)

theorem exists_lift {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R] (x' : Sp R ⟶ S')
    (u : epsAt (x' ≫ f) ⟶ G) :
    ∃ v : epsAt x' ⟶ G', lf v ≫ φ = lf u ∧ (IsTanAt G (x' ≫ f) u → IsTanAt G' x' v) := by
  obtain ⟨v, rfl⟩ := (LiePull.tanPts h x').surjective u
  exact ⟨v, rfl, (LiePull.isTan_iff h x' v).1⟩

theorem hodge_congr {S : Scheme.{0}} {G : Over S} [GrpObj G] (Lb : LB G.left) {z z' : Sp ℂ ⟶ S} (h : z = z')
    {v w : epsAt z ⟶ G} {v' w' : epsAt z' ⟶ G} (hv : lf v = lf v') (hw : lf w = lf w') {c : ℂ}
    (hc : HodgeIP G Lb z v w c) : HodgeIP G Lb z' v' w' c := by
  subst h
  obtain rfl : v = v' := Over.OverMorphism.ext hv
  obtain rfl : w = w' := Over.OverMorphism.ext hw
  exact hc

end PositivityTheory.Xgn.QuotientUniformizationConjugate

open PositivityTheory.Xgn.QuotientUniformizationConjugate in
theorem PositivityTheory.Xgn.height_bound_complex_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel t.G ξ Li) (K : Type) (J : K → Type) (y : (Σ k, J k) → Ω) (h : LieMetric M y) (C : ℝ) (z : Sp ℂ ⟶ X), AbBound t h C (spMap (starRingEnd ℂ) ≫ z) → AbBound t h C z := by
  intro E _ _ _ H X t Ω _ ξ Li _ _ M K J y h C z hb P
  obtain ⟨P', mK, mB, c1, c2⟩ := GlobalTheory.T.abelian_part_base_change E H X t ℂ ℂ z P (starRingEnd ℂ)
  obtain ⟨hp, hb'⟩ := hb P'
  refine ⟨(CoverDenseAlt.isPrincipal_iff_of_base_change E H ℂ ℂ (starRingEnd ℂ) P.tB P'.tB mB).1 hp, fun v v₀ c hv hv₀ hc => ?_⟩
  have hid : 𝟙 (Sp ℂ) ≫ spMap (starRingEnd ℂ) = spMap (starRingEnd ℂ) ≫ 𝟙 (Sp ℂ) := by
    rw [Category.id_comp, Category.comp_id]
  obtain ⟨u, hu, hut⟩ := exists_bc (starRingEnd ℂ) (𝟙 (Sp ℂ)) _ hid v
  obtain ⟨v', hv', hvt⟩ := exists_lift mK.cart (𝟙 (Sp ℂ)) u
  obtain ⟨v₀', hv₀', -⟩ := exists_bc (starRingEnd ℂ) z _ rfl v₀
  obtain ⟨a, ha, -⟩ := exists_bc (starRingEnd ℂ) (𝟙 (Sp ℂ)) _ rfl (v ≫ P.τ.q ≫ P.e.hom)
  obtain ⟨b, hb₁, -⟩ := exists_bc (starRingEnd ℂ) (𝟙 (Sp ℂ)) _ hid (v ≫ P.τ.q ≫ P.e.hom)
  have hv'' : lf v' ≫ mK.φ = spMap (dualMap (starRingEnd ℂ)) ≫ lf v := hv'.trans hu
  have hv₀'' : lf v ≫ P.m.φ = lf v₀ := hv₀
  have e₁ : lf v' ≫ P'.m.φ = lf v₀' := by
    rw [← c1, ← Category.assoc, hv'', Category.assoc, hv₀'', hv₀']
  have e₂ : lf (v' ≫ P'.τ.q ≫ P'.e.hom) ≫ mB.φ = lf b := by
    have s₁ : lf (v' ≫ P'.τ.q ≫ P'.e.hom) = lf v' ≫ (P'.τ.q ≫ P'.e.hom).left := rfl
    have s₂ : lf (v ≫ P.τ.q ≫ P.e.hom) = lf v ≫ (P.τ.q ≫ P.e.hom).left := rfl
    rw [hb₁, s₁, s₂, Category.assoc, ← c2, ← Category.assoc, hv'', Category.assoc]
  have h₁ := GlobalTheory.T.hodge_inner_product_conjugate E H (Sp ℂ) P.tB (𝟙 _) _ _ a a c ha ha hc
  have hab : lf a = lf b := ha.trans hb₁.symm
  have h₂ := hodge_congr P.tB.PP.L hid.symm hab hab h₁
  have h₃ := ((GlobalTheory.T.hodge_inner_product_pullback_unique E H (Sp ℂ) (Sp ℂ) P'.tB P.tB (spMap (starRingEnd ℂ)) mB (𝟙 _) _ _ b b e₂ e₂).1 _).2 h₂
  have h₄ := hb' v' v₀' _ (hvt (hut hv)) e₁ h₃
  rw [h.conj z v₀ v₀ v₀' v₀' hv₀' hv₀', Complex.conj_re, Complex.conj_re] at h₄
  exact h₄
