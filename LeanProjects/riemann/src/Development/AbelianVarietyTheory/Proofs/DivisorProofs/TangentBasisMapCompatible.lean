import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecValAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FrameCoordUnit

theorem coord_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (A : Type) [CommRing A] (ξ : Sp A ⟶ Y.X) (g : ℕ)
    (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)), IsTanBasis Y.t ξ e →
    ∀ (σ : E →+* ℂ) (U h : Fin (Dw.mult σ) → Fin g → A), IsUnit (pairDet h U) →
    ∀ (L : Type) [CommRing L] [Algebra c.F L] (io : A →+* L) (yL : Sp L ⟶ Xo'.XF c'), yL ≫ Y.j = spMap io ≫ ξ →
    ∀ z₀ : FrPt Xo c L, z₀.x = yL ≫ r ≫ pullback.fst _ _ →
    ∀ w : Fin (Dw.mult σ) → (Sp (DualNumber L) ⟶ Y.oF.t.G.left),
      (∀ i, IsCombAtG Y.t (yL ≫ Y.j) (bcV Y.t io e) (fun b => io (U i b)) (w i ≫ Y.m.φ)) →
      (∀ i, IsTanAtG Y.oF.t yL (w i)) → (∀ i, IsEigAt c σ (w i ≫ ν.φ)) →
      ∃ g₁ : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L, IsUnit g₁.det ∧
        ∀ i, IsCombAt z₀.x (z₀.u σ) (g₁ i) (w i ≫ ν.φ) := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν A _ ξ g e he σ U h hU L _ _ io yL hyL z₀ hz₀ w hwc hwt hwe
  have ht1 : ∀ i, IsTanAt z₀.x (w i ≫ ν.φ) := fun i => by
    have := (GlobalTheory.LocM.BaseMdl.tan_push ν (hwt i).1).1 (hwt i)
    rw [hz₀]; exact this
  choose g₁ hg₁ using fun i => (z₀.basis σ (w i ≫ ν.φ) (ht1 i) (hwe i)).exists
  have hub : ∀ j, z₀.u σ j ≫ Xo.univ.t.G.hom =
      spMap (algebraMap L (DualNumber L)) ≫ yL ≫ r ≫ pullback.fst _ _ := fun j => by
    rw [← hz₀]; exact (z₀.tan σ j).1
  choose q hq1 hq2 using fun j => GlobalTheory.LocM.BaseMdl.exists_lift ν (x' := yL) (hub j)
  have hqt : ∀ j, IsTanAtG Y.oF.t yL (q j) := fun j =>
    (GlobalTheory.LocM.BaseMdl.tan_push ν (hq2 j)).2 (by rw [hq1, ← hz₀]; exact z₀.tan σ j)
  have hqt' : ∀ j, IsTanAtG Y.t (spMap io ≫ ξ) (q j ≫ Y.m.φ) := fun j => by
    rw [← hyL]; exact (GlobalTheory.LocM.BaseMdl.tan_push Y.m (hq2 j)).1 (hqt j)
  choose Q hQ using fun j => (he.2 L io (q j ≫ Y.m.φ) (hqt' j)).exists
  have hqb : ∀ j (a : L), (spMap (epsMul a) ≫ q j) ≫ Y.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ yL :=
    fun j a => by rw [Category.assoc, hq2, ← Category.assoc, GlobalTheory.LocM.BaseMdl.epsMul_comp]
  have hcomb : ∀ i, IsCombAtG Y.oF.t yL q (g₁ i) (w i) := fun i => by
    let u : Fin (Dw.mult σ) → (tEpsG yL ⟶ Y.oF.t.G) := fun j => Over.homMk (spMap (epsMul (g₁ i j)) ≫ q j) (hqb j _)
    have hc : IsCombAtG Y.oF.t yL q (g₁ i) (List.ofFn u).prod.left := ⟨u, fun _ => rfl, rfl⟩
    have hcb : (List.ofFn u).prod.left ≫ Y.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ yL :=
      Over.w (List.ofFn u).prod
    have hc2 := (GlobalTheory.LocM.BaseMdl.comb_push ν hq2 (g₁ i) hcb).1 hc
    have hq1' : (fun j => q j ≫ ν.φ) = z₀.u σ := funext hq1
    rw [hq1', ← hz₀] at hc2
    have heq : (List.ofFn u).prod.left ≫ ν.φ = w i ≫ ν.φ :=
      GlobalTheory.FlatModel.LiftBC.isCombAtG_unique Xo.univ.t hc2 (hg₁ i)
    have heq2 : (List.ofFn u).prod.left = w i := ν.cart.1.hom_ext heq (hcb.trans (hwt i).1.symm)
    rw [← heq2]; exact hc
  have hwt' : ∀ i, IsTanAtG Y.t (spMap io ≫ ξ) (w i ≫ Y.m.φ) := fun i => by
    rw [← hyL]; exact (GlobalTheory.LocM.BaseMdl.tan_push Y.m (hwt i).1).1 (hwt i)
  have hcomb' : ∀ i, IsCombAtG Y.t (spMap io ≫ ξ) (fun j => q j ≫ Y.m.φ) (g₁ i) (w i ≫ Y.m.φ) := fun i => by
    rw [← hyL]; exact (GlobalTheory.LocM.BaseMdl.comb_push Y.m hq2 (g₁ i) (hwt i).1).1 (hcomb i)
  have hbt : ∀ b, IsTanAtG Y.t (spMap io ≫ ξ) (spMap (dualMap io) ≫ e b) :=
    (GlobalTheory.FlatModel.isTanBasis_bc he io).1
  have hcoef : ∀ i b, io (U i b) = ∑ j, Q j b * g₁ i j := fun i b => by
    have h1 := GlobalTheory.TangentLinear.isCombAtG_mulVec (fun b => spMap (dualMap io) ≫ e b) hbt
      (fun j => q j ≫ Y.m.φ) (Matrix.of fun b j => Q j b) (g₁ i) (w i ≫ Y.m.φ) (fun j => hQ j) (hcomb' i)
    have h2 : IsCombAtG Y.t (spMap io ≫ ξ) (fun b => spMap (dualMap io) ≫ e b) (fun b => io (U i b)) (w i ≫ Y.m.φ) := by
      rw [← hyL]; exact hwc i
    have := (he.2 L io (w i ≫ Y.m.φ) (hwt' i)).unique h2 h1
    have := congrFun this b
    simpa [Matrix.mulVec, dotProduct] using this
  refine ⟨Matrix.of g₁, ?_, fun i => hg₁ i⟩
  let M : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) L := Matrix.of fun j k' => ∑ b, Q j b * io (h k' b)
  have hdet : io (pairDet h U) = (Matrix.of g₁ * M).det := by
    rw [pairDet, RingHom.map_det]
    congr 1
    ext k k'
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, hcoef,
      Matrix.mul_apply, M, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
  have hu := hU.map io
  rw [hdet, Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

end GlobalTheory.FrameCoordUnit
