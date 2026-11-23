import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

noncomputable section

namespace GlobalTheory.FlatModel.GenericPush

theorem one_left_eq {S T : Scheme.{0}} (x : T ⟶ S) (G : Over S) [GrpObj G] :
    (1 : Over.mk x ⟶ G).left = x ≫ η[G].left := rfl

theorem eps_alg' {S : Type} [CommRing S] (a : S) :
    spMap (epsMul a) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap S (DualNumber S)) := by
  rw [← Geo.Tor.spMap_comp]
  congr 1
  exact RingHom.ext fun x => by ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.FlatModel.GenericPush

open GlobalTheory.FlatModel.GenericPush in

theorem GlobalTheory.FlatModel.tan_eig_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (L : Type) [CommRing L] [Algebra c.F L]
    (yL : Sp L ⟶ Xo'.XF c') (σ : E →+* ℂ) (s : 𝓞 E →+* L), (∀ a, algebraMap c.F L (embK c σ a) = s a) →
    ∀ w : Sp (DualNumber L) ⟶ Y.oF.t.G.left, IsTanAtG Y.oF.t yL w → IsEigG Y.t s (w ≫ Y.m.φ) →
      IsTanAt (yL ≫ r ≫ pullback.fst _ _) (w ≫ ν.φ) ∧ IsEigAt c σ (w ≫ ν.φ) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν L _ _ yL σ s hs w hT hE
  have he : η[Y.oF.t.G].left ≫ ν.φ = (r ≫ pullback.fst _ _) ≫ η[Xo.univ.t.G].left := by
    have h0 := ν.cm.e_comm
    rw [ν.base] at h0
    exact h0
  refine ⟨⟨?_, ?_⟩, fun a => ?_⟩
  · rw [Category.assoc, ν.cart.1.w, ← Category.assoc, hT.1, Category.assoc]
  · rw [← Category.assoc, hT.2, one_left_eq, one_left_eq, Category.assoc, he]
    simp only [Category.assoc]
  · have key : w ≫ (Y.oF.t.act.act a).left = spMap (epsMul (s a)) ≫ w := by
      apply Y.m.cart.1.hom_ext
      · rw [Category.assoc, Y.m.act, ← Category.assoc, hE a, Category.assoc]
      · rw [Category.assoc, Over.w, Category.assoc, hT.1, ← Category.assoc, eps_alg']
    show (w ≫ ν.φ) ≫ (Xo.univ.t.act.act a).left = spMap (epsMul (algebraMap c.F L (embK c σ a))) ≫ w ≫ ν.φ
    rw [hs, Category.assoc, ← ν.act, ← Category.assoc, key, Category.assoc]

end
