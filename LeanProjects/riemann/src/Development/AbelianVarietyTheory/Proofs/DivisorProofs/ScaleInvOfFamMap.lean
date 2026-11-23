import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LineConst

open Polynomial

variable (k : Type) [Field k]

def scaleHom (R : Type) [CommRing R] [Algebra k R] (u : R) : Polynomial k →+* Polynomial R :=
  Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap k R)) (Polynomial.C u * Polynomial.X)

theorem scaleHom_algebraMap (R : Type) [CommRing R] [Algebra k R] (u : R) :
    (scaleHom k R u).comp (algebraMap k (Polynomial k)) = algebraMap k (Polynomial R) := by
  ext a
  simp [scaleHom, Polynomial.algebraMap_apply]

def lineOver (R : Type) [CommRing R] [Algebra k R] : Over (Sp k) :=
  Over.mk (spMap (algebraMap k (Polynomial R)))

variable {k}

def scaled (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] (u : R) :
    lineOver k R ⟶ B :=
  Over.homMk (spMap (scaleHom k R u) ≫ f) (by
    change spMap (scaleHom k R u) ≫ f ≫ B.hom = spMap (algebraMap k (Polynomial R))
    rw [hf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, scaleHom_algebraMap])

def famMap (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] (u : R) : Sp (Polynomial R) ⟶ B.left :=
  (scaled B f hf R u * (scaled B f hf R 1)⁻¹).left

end GlobalTheory.LineConst

namespace GlobalTheory.LineConst
open Polynomial

theorem scaleHom_comp_map {k : Type} [Field k] {R R' : Type} [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R']
    (φ : R →ₐ[k] R') (u : R) :
    (Polynomial.mapRingHom (φ : R →+* R')).comp (scaleHom k R u) = scaleHom k R' (φ u) := by
  apply Polynomial.ringHom_ext
  · intro a; simp [scaleHom]
  · simp [scaleHom]

def lineMap {k : Type} [Field k] {R R' : Type} [CommRing R] [Algebra k R] [CommRing R'] [Algebra k R']
    (φ : R →ₐ[k] R') : lineOver k R' ⟶ lineOver k R :=
  Over.homMk (spMap (Polynomial.mapRingHom (φ : R →+* R'))) (by
    change spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ spMap (algebraMap k (Polynomial R)) =
      spMap (algebraMap k (Polynomial R'))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a; simp [Polynomial.algebraMap_apply])

theorem lineMap_scaled {k : Type} [Field k] (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) {R R' : Type} [CommRing R] [Algebra k R]
    [CommRing R'] [Algebra k R'] (φ : R →ₐ[k] R') (u : R) :
    lineMap φ ≫ scaled B f hf R u = scaled B f hf R' (φ u) := by
  ext1
  change spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ spMap (scaleHom k R u) ≫ f =
    spMap (scaleHom k R' (φ u)) ≫ f
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, scaleHom_comp_map]

theorem famMap_base {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) {R R' : Type} [CommRing R] [Algebra k R]
    [CommRing R'] [Algebra k R'] (φ : R →ₐ[k] R') (u : R) :
    spMap (Polynomial.mapRingHom (φ : R →+* R')) ≫ famMap B f hf R u = famMap B f hf R' (φ u) := by
  have h := congrArg CommaMorphism.left
    (show lineMap φ ≫ (scaled B f hf R u * (scaled B f hf R 1)⁻¹) =
      scaled B f hf R' (φ u) * (scaled B f hf R' 1)⁻¹ by
      rw [MonObj.comp_mul, GrpObj.comp_inv, lineMap_scaled, lineMap_scaled, map_one])
  exact h

theorem famMap_one {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (R : Type) [CommRing R] [Algebra k R] :
    famMap B f hf R 1 = spMap (algebraMap k (Polynomial R)) ≫ (η[B] : 𝟙_ (Over (Sp k)) ⟶ B).left := by
  unfold famMap
  rw [mul_inv_cancel, Hom.one_def, Over.comp_left]
  congr 1

end GlobalTheory.LineConst

namespace GlobalTheory.LineConst
open Polynomial

def linePt {k : Type} [Field k] (a : k) : 𝟙_ (Over (Sp k)) ⟶ lineOver k k :=
  Over.homMk (spMap (Polynomial.evalRingHom a)) (by
    change spMap (Polynomial.evalRingHom a) ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.evalRingHom a).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id])

theorem linePt_scaled_left {k : Type} [Field k] (B : Over (Sp k)) (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (a c : k) :
    (linePt a ≫ scaled B f hf k c).left = spMap (Polynomial.evalRingHom (c * a)) ≫ f := by
  change spMap (Polynomial.evalRingHom a) ≫ spMap (scaleHom k k c) ≫ f = _
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  apply Polynomial.ringHom_ext
  · intro z; simp [scaleHom]
  · simp [scaleHom]

theorem scale_inv_of_famMap {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (f : Sp (Polynomial k) ⟶ B.left)
    (hf : f ≫ B.hom = spMap (algebraMap k (Polynomial k))) (c : k)
    (h : famMap B f hf k c = spMap (algebraMap k (Polynomial k)) ≫ spMap (Polynomial.evalRingHom 0) ≫ famMap B f hf k c)
    (a : k) : spMap (Polynomial.evalRingHom (c * a)) ≫ f = spMap (Polynomial.evalRingHom a) ≫ f := by
  have hpt : ∀ b : k, spMap (Polynomial.evalRingHom b) ≫ spMap (algebraMap k (Polynomial k)) = 𝟙 _ := by
    intro b
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (Polynomial.evalRingHom b).comp (algebraMap k (Polynomial k)) = RingHom.id k := by
      ext z; simp
    rw [this, CommRingCat.ofHom_id, Spec.map_id]
  have hleft : spMap (Polynomial.evalRingHom a) ≫ famMap B f hf k c =
      spMap (Polynomial.evalRingHom 0) ≫ famMap B f hf k c := by
    conv_lhs => rw [h]
    rw [← Category.assoc, hpt, Category.id_comp]
  have hq : ∀ b : k, linePt b ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) =
      (linePt b ≫ scaled B f hf k c) * (linePt b ≫ scaled B f hf k 1)⁻¹ := by
    intro b; rw [MonObj.comp_mul, GrpObj.comp_inv]
  have h0 : linePt 0 ≫ scaled B f hf k c = linePt 0 ≫ scaled B f hf k 1 := by
    ext1
    rw [linePt_scaled_left, linePt_scaled_left, mul_zero, mul_zero]
  have hall : linePt a ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) =
      linePt 0 ≫ (scaled B f hf k c * (scaled B f hf k 1)⁻¹) := by
    ext1
    exact hleft
  rw [hq, hq, h0, mul_inv_cancel] at hall
  have hall' : linePt a ≫ scaled B f hf k c = linePt a ≫ scaled B f hf k 1 :=
    mul_inv_eq_one.mp hall
  have h2 := congrArg CommaMorphism.left hall'
  have e1 := linePt_scaled_left B f hf a c
  have e2 := linePt_scaled_left B f hf a 1
  rw [_root_.one_mul] at e2
  rw [← e1, ← e2]
  exact h2

end GlobalTheory.LineConst
