import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModelPAdicComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BLieLieComb

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem spMap_epsMul_algebraMap {R : Type} [CommRing R] (s : R) :
    spMap (epsMul s) ≫ spMap (algebraMap R (DualNumber R)) = spMap (algebraMap R (DualNumber R)) := by
  rw [spMap, spMap, ← Spec.map_comp]
  congr 1
  ext x
  · simp [epsMul]
  · simp [epsMul, TrivSqZeroExt.map]

theorem tanEig_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]]
    (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (y : FrPt Xo c ℂ_[p]), GlobalTheory.AllWt.ptF y = yy ≫ r →
    ∀ w : Sp (DualNumber ℂ_[p]) ⟶ Y.oF.t.G.left, w ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ_[p] (DualNumber ℂ_[p])) ≫ yy →
    spMap (TrivSqZeroExt.fstHom ℂ_[p] ℂ_[p] ℂ_[p]).toRingHom ≫ w = (1 : Over.mk yy ⟶ Y.oF.t.G).left →
    ∀ σ : E →+* ℂ, (∀ a : 𝓞 E, (w ≫ Y.m.φ) ≫ (Y.t.act.act a).left =
      spMap (epsMul (algebraMap c.F ℂ_[p] (embK c σ a))) ≫ w ≫ Y.m.φ) →
    IsTanAt y.x (w ≫ ν.φ) ∧ IsEigAt c σ (w ≫ ν.φ) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν p _ _ yy y hy w hw h1 σ he
  have hx : yy ≫ r ≫ pullback.fst _ _ = y.x := by
    have h0 : GlobalTheory.AllWt.ptF y ≫ pullback.fst _ _ = y.x := pullback.lift_fst _ _ _
    rw [hy, Category.assoc] at h0
    exact h0
  have hsq : ν.φ ≫ Xo.univ.t.G.hom = Y.oF.t.G.hom ≫ r ≫ pullback.fst _ _ := ν.cart.1.w
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hsq, ← Category.assoc, hw, Category.assoc, hx]
  · let T : Over (Xo'.XF c') := Over.mk yy
    have hu : ((1 : T ⟶ Y.oF.t.G).left ≫ ν.φ) ≫ Xo.univ.t.G.hom = T.hom ≫ (r ≫ pullback.fst _ _) := by
      rw [Category.assoc, hsq, ← Category.assoc, Over.w]
    let x₀ : Over.mk (T.hom ≫ (r ≫ pullback.fst _ _)) ⟶ Xo.univ.t.G := Over.homMk ((1 : T ⟶ Y.oF.t.G).left ≫ ν.φ) hu
    have hm := ν.cart.2 T 1 1 x₀ x₀ rfl rfl
    have hxx : x₀ * x₀ = x₀ * 1 := by
      rw [_root_.mul_one]
      ext1
      rw [hm, _root_.mul_one]
      rfl
    have h11 : x₀ = 1 := mul_left_cancel hxx
    have key : ∀ (m m' : Sp ℂ_[p] ⟶ Xo.X), m = m' →
        (1 : Over.mk m ⟶ Xo.univ.t.G).left = (1 : Over.mk m' ⟶ Xo.univ.t.G).left := by
      rintro _ _ rfl; rfl
    rw [← Category.assoc, h1]
    have : x₀.left = (1 : Over.mk (T.hom ≫ (r ≫ pullback.fst _ _)) ⟶ Xo.univ.t.G).left := by rw [h11]
    exact this.trans (key _ _ hx)
  · intro a
    have hA : w ≫ (Y.oF.t.act.act a).left =
        spMap (epsMul (algebraMap c.F ℂ_[p] (embK c σ a))) ≫ w := by
      apply Y.m.cart.1.hom_ext
      · rw [Category.assoc, Y.m.act a, ← Category.assoc, he a, Category.assoc]
      · rw [Category.assoc, Over.w, hw, Category.assoc, hw, ← Category.assoc, spMap_epsMul_algebraMap]
    rw [Category.assoc, ← ν.act a, ← Category.assoc, hA, Category.assoc]

end GlobalTheory.FlatModel
