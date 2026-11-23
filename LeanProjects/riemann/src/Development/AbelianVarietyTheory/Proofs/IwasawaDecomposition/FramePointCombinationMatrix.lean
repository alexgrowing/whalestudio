import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramTransformOfCoordinateChangeImports
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpFourClauses
import Formalism.LocalToGlobal.ProjectiveLattices.OpenRowsFree

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.FramePairGram
open Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace GlobalTheory.FramePairGram

attribute [local instance] Over.cartesianMonoidalCategory

section Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X X' : Scheme.{0}}
  {t : SAB H X} {t' : SAB H X'} {S : Type} [CommRing S] {f : X' ⟶ X}

theorem left_pushE_symm_congr (m : SABMap t' t f) {q q' : Sp S ⟶ X'} (e : q = q') {x₀ x₀' : Sp S ⟶ X}
    (hq : q ≫ f = x₀) (hq' : q' ≫ f = x₀') {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x₀ v)
    (hv' : IsTanAtG t x₀' v) :
    (tv ((pushE m q hq).symm (tanOf hv))).left = (tv ((pushE m q' hq').symm (tanOf hv'))).left := by
  subst e
  subst hq
  subst hq'
  rfl

end Generic

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

theorem ptF_eq_of_x_eq {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : y.x = y'.x) :
    GlobalTheory.AllWt.ptF y = GlobalTheory.AllWt.ptF y' :=
  pullback.hom_ext ((ptF_fst y).trans (h.trans (ptF_fst y').symm)) ((ptF_snd y).trans (ptF_snd y').symm)

theorem ofFrPt_v_eq {S : Type} [CommRing S] [Algebra c.F S] {y y' : FrPt Xo c S} (h : y.x = y'.x)
    {x : Sp S ⟶ Z.X} (hx : GlobalTheory.AllWt.ptF y ≫ Z.jQ ≫ genι Z = x) {x' : Sp S ⟶ Z.X}
    (hx' : GlobalTheory.AllWt.ptF y' ≫ Z.jQ ≫ genι Z = x') (τ : E →+* ℂ) (i : Fin (Dw.mult τ))
    (hv : IsTanAtG Xo.univ.t y'.x (y.u τ i)) :
    (EigFrame.ofFrPt Z y hx).v τ i = (tv (lieEquiv Z y' hx' (tanOf hv))).left := by
  show (tv (pushE Z.m (GlobalTheory.AllWt.ptF y) hx
      ((pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y) (ptF_fst y)).symm (tanOf (t := Xo.univ.t) (y.tan τ i))))).left =
    (tv (pushE Z.m (GlobalTheory.AllWt.ptF y') hx'
      ((pushE Z.m0.toSABMap (GlobalTheory.AllWt.ptF y') (ptF_fst y')).symm (tanOf hv)))).left
  rw [left_pushE, left_pushE,
    left_pushE_symm_congr Z.m0.toSABMap (ptF_eq_of_x_eq h) (ptF_fst y) (ptF_fst y') (y.tan τ i) hv]

theorem isComb_ofFrPt {S : Type} [CommRing S] [Algebra c.F S] (y' : FrPt Xo c S) {x' : Sp S ⟶ Z.X}
    (hx' : GlobalTheory.AllWt.ptF y' ≫ Z.jQ ≫ genι Z = x') (τ : E →+* ℂ) (a : Fin (Dw.mult τ) → S)
    {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAtG Xo.univ.t y'.x w)
    (hc : IsCombAtG Xo.univ.t y'.x (y'.u τ) a w) :
    IsCombAtG Z.t x' ((EigFrame.ofFrPt Z y' hx').v τ) a (tv (lieEquiv Z y' hx' (tanOf hv))).left := by
  have e := (isComb_iff (t := Xo.univ.t) (x := y'.x) (fun b => tanOf (t := Xo.univ.t) (y'.tan τ b)) a (tanOf hv)).1 hc
  refine (isComb_iff (t := Z.t) (x := x') (fun b => lieEquiv Z y' hx' (tanOf (t := Xo.univ.t) (y'.tan τ b))) a
    (lieEquiv Z y' hx' (tanOf hv))).2 ?_
  rw [e, map_sum]
  simp only [map_smul]

variable [SmoothOfRelativeDimension Dw.dim (genStr Z)]

theorem gram_transport (x : OddPrimesWithRootsOfUnity Z) {σ : c.F →+* ℂ} {p q : CxPts (genStr Z) σ} (e : p = q)
    (F : EigFrame Z σ (p.1 ≫ genι Z)) (G : EigFrame Z σ (q.1 ≫ genι Z)) (τ : E →+* ℂ)
    (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (h : ∀ i, IsCombAtG Z.t (q.1 ≫ genι Z) (G.v τ) (fun a => T a i) (F.v τ i)) :
    x.gram p F τ = Tᴴ * x.gram q G τ * T := by
  subst e
  exact x.gram_change G F τ T h

theorem gram_of_comb (x : OddPrimesWithRootsOfUnity Z) {σ : c.F →+* ℂ} (y y' : FrPt Xo c (CAt σ)) (h : y.x = y'.x) (τ : E →+* ℂ)
    (K : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)
    (hK : ∀ i, Formalism.L2.Pj.IsCombAt y'.x (y'.u τ) (fun b => (K b i : CAt σ)) (y.u τ i)) :
    x.gram (cxPt Z y) (cxFrame Z y) τ = Kᴴ * x.gram (cxPt Z y') (cxFrame Z y') τ * K := by
  refine gram_transport x (cxPt_congr h) _ _ τ K fun i => ?_
  have hv : IsTanAtG Xo.univ.t y'.x (y.u τ i) := h ▸ y.tan τ i
  have hx' : GlobalTheory.AllWt.ptF (S := CAt σ) y' ≫ Z.jQ ≫ genι Z = (cxPt Z y').1 ≫ genι Z := (Category.assoc _ _ _).symm
  have hx : GlobalTheory.AllWt.ptF (S := CAt σ) y ≫ Z.jQ ≫ genι Z = (cxPt Z y).1 ≫ genι Z := (Category.assoc _ _ _).symm
  have e1 : (cxFrame Z y).v τ i = (tv (lieEquiv Z y' hx' (tanOf hv))).left := ofFrPt_v_eq h hx hx' τ i hv
  rw [e1]
  exact isComb_ofFrPt (S := CAt σ) y' hx' τ (fun b => (K b i : CAt σ)) hv (hK i)

end Main

end GlobalTheory.FramePairGram
