import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TanComb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {V : Type} [CommRing V]

def push (x : Sp V ⟶ Y.X) {G : SAB H (Sp V)} (ψ : SABMap G Y.t x) (q : epsOver V V ⟶ G.G) :
    overAt x (DualNumber V) ⟶ Y.t.G :=
  Over.homMk (q.left ≫ ψ.φ) (by
    have hw := ψ.cart.1.w
    simp only [Category.assoc, hw]
    rw [← Category.assoc, Over.w q]
    rfl)

theorem push_mul (x : Sp V ⟶ Y.X) {G : SAB H (Sp V)} (ψ : SABMap G Y.t x) (p q : epsOver V V ⟶ G.G) :
    push x ψ (p * q) = push x ψ p * push x ψ q := by
  apply Over.OverMorphism.ext
  exact (ψ.cart.2 (epsOver V V) p q (push x ψ p) (push x ψ q) rfl rfl).symm

theorem push_one (x : Sp V ⟶ Y.X) {G : SAB H (Sp V)} (ψ : SABMap G Y.t x) :
    push x ψ 1 = 1 := by
  have h : push x ψ 1 * push x ψ 1 = push x ψ 1 := by
    rw [← push_mul, _root_.mul_one]
  exact mul_eq_left.1 h

def pushHom (x : Sp V ⟶ Y.X) {G : SAB H (Sp V)} (ψ : SABMap G Y.t x) :
    (epsOver V V ⟶ G.G) →* (overAt x (DualNumber V) ⟶ Y.t.G) where
  toFun := push x ψ
  map_one' := push_one x ψ
  map_mul' := push_mul x ψ

end GlobalTheory.TanComb

open GlobalTheory.TanComb in

theorem GlobalTheory.TanComb.tanComb : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {V : Type} [CommRing V] (x : Sp V ⟶ Y.X) (G : SAB H (Sp V)) (ψ : SABMap G Y.t x) {m : ℕ} (ub : Fin m → (epsOver V V ⟶ G.G)) (ub' : Fin m → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G) (a : Fin m → V) (w : epsOver V V ⟶ G.G) (v : ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM x Y.t.G), (∀ i, (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (ub' i)).left = (ub i).left ≫ ψ.φ) → (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv v).left = w.left ≫ ψ.φ → IsComb ub a w → ∑ i, a i • ub' i = v := by
  intro E _ _ _ H Dw l Xo c O _ β Y V _ x G ψ m ub ub' a w v hub hv hw
  obtain ⟨u, hu, rfl⟩ := hw
  apply GlobalTheory.FlagMod.tan_ext_left
  rw [hv, GlobalTheory.FlagMod.tv_sum']
  have key : ∏ i, ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (a i • ub' i) = pushHom x ψ (List.ofFn u).prod := by
    rw [map_list_prod, List.map_ofFn, List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    apply Over.OverMorphism.ext
    show (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (a i • ub' i)).left = (u i).left ≫ ψ.φ
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_smul, smT_left, hub i, hu i, Category.assoc]
  rw [key]
  rfl

end
