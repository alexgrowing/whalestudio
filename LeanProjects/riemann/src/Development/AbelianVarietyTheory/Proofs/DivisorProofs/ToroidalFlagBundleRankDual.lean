import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMatrixChangeOfFrameStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open GlobalTheory.FlagCls

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

section Free

open ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β}

theorem comb_eq {X : Scheme.{0}} {t : SAB H X} {K : Type} [CommRing K] {x : Sp K ⟶ X} {m : ℕ}
    {u : Fin m → (Sp (DualNumber K) ⟶ t.G.left)} {a : Fin m → K} {w w' : Sp (DualNumber K) ⟶ t.G.left}
    (h : IsCombAtG t x u a w) (h' : IsCombAtG t x u a w') : w = w' := by
  obtain ⟨p, hp, hp'⟩ := h
  obtain ⟨q, hq, hq'⟩ := h'
  have e : p = q := by
    funext i
    exact Over.OverMorphism.ext ((hp i).trans (hq i).symm)
  rw [← hp', ← hq', e]

theorem coord_change {K : Type} [CommRing K] {χ : c.F →+* K} {x : Sp K ⟶ Z.X} {τ : E →+* ℂ} {m : ℕ}
    {u u' : Fin m → (Sp (DualNumber K) ⟶ Z.t.G.left)} (hu : IsEigBasis Z χ x τ u) (hu' : IsEigBasis Z χ x τ u')
    (S : Matrix (Fin m) (Fin m) K) (hS : ∀ j, IsCombAtG Z.t x u (S j) (u' j)) {a a' : Fin m → K}
    {w : Sp (DualNumber K) ⟶ Z.t.G.left} (h : IsCombAtG Z.t x u a w) (h' : IsCombAtG Z.t x u' a' w) :
    a = Matrix.vecMul a' S := by
  let U : Fin m → TanM x Z.t.G := fun b => tanOf (hu.1 b).1
  let U' : Fin m → TanM x Z.t.G := fun b => tanOf (hu'.1 b).1
  have e1 : ∀ j, U' j = ∑ b, S j b • U b := fun j => (isComb_iff U _ (U' j)).1 (hS j)
  obtain rfl : w = (tv (∑ j, a' j • U' j)).left := comb_eq h' ((isComb_iff U' a' _).2 rfl)
  have hw : IsEigTan Z χ x τ (tv (∑ j, a' j • U' j)).left := by
    refine ⟨isTan_tv _, fun o => ?_⟩
    have e2 : ∀ j, actR Z.t.act o (U' j) = χ (embK c τ o) • U' j := fun j => tan_ext ((hu'.1 j).2 o)
    have e3 : actR Z.t.act o (∑ j, a' j • U' j) = χ (embK c τ o) • ∑ j, a' j • U' j := by
      simp only [map_sum, map_smul, e2, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _
    exact congrArg (fun z => (tv z).left) e3
  refine (hu.2 _ hw).unique h ((isComb_iff U _ _).2 ?_)
  simp only [e1, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
  exact Finset.sum_comm

end Free

theorem agreeAt_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Oz : Type) [CommRing Oz] (β : Oz →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (r : ℕ) (τ : E →+* ℂ) (dual : Bool) (Bs Bg Y : Scheme.{0}) (M : Bs.Modules) (hM : IsVB M r) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen Z) (u : FrAssign Z M r jB) (π : Y ⟶ Bs) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r), IsLieFrames Z e jB πB M r τ dual u → ∀ (K : Type) [CommRing K] (y : Sp K ⟶ Y) (xb : Sp K ⟶ Bg) (χ : c.F →+* K), y ≫ π = xb ≫ jB → xb ≫ πB ≫ genStr Z = spMap χ → ∀ (v : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)) (V : Bs.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (hx : ⊤ ≤ (xb ≫ jB) ⁻¹ᵁ V) (d : Matrix (Fin r) (Fin r) K), IsUnit d.det → (∀ i, IsCombAtG Z.t (xb ≫ πB ≫ genι Z) (u V f hf K xb hx) (d i) (v i)) → FlagMat hM π fl hf y (lieMat dual d) → AgreeAt Z hM jB u π fl dual y xb (xb ≫ πB ≫ genι Z) v := by
  intro E _ _ _ H Dw l Xo c Oz _ β Z F _ e r τ dual Bs Bg Y M hM jB πB u π fl hL K _ y xb χ hy hχ v V f hf hx d hd hv hA
    V' f' hf' hx' d' hv'
  have hχ' : (χ.comp e.toRingHom).comp e.symm.toRingHom = χ := RingHom.ext fun z => by simp
  have hb : ∀ (U : Bs.Opens) (g : Fin r → Γ(M, U)) (hg : IsFrame g) (hU : ⊤ ≤ (xb ≫ jB) ⁻¹ᵁ U),
      IsEigBasis Z χ (xb ≫ πB ≫ genι Z) τ (u U g hg K xb hU) := fun U g hg hU => by
    have := hL.1 U g hg K xb hU (χ.comp e.toRingHom) (by
      have h1 := congrArg (· ≫ spMap e.toRingHom) hχ
      simp only [Category.assoc] at h1
      rw [h1]
      exact (Spec.map_comp _ _).symm)
    rwa [hχ'] at this
  have hxx : ⊤ ≤ (xb ≫ jB) ⁻¹ᵁ (V' ⊓ V) := fun p hp => ⟨hx' hp, hx hp⟩
  obtain ⟨hS, hF⟩ := GlobalTheory.T.flag_matrix_change_of_frame Bs Y M r hM π fl V' f' hf' V f hf K y (xb ≫ jB) hxx _ hy hA
  have h2 := hL.2.1 V' V f' f hf' hf K xb hx' hx hxx
  set S : Matrix (Fin r) (Fin r) K :=
    Matrix.of fun a b => TangentOrigin.evalPt (xb ≫ jB) (V' ⊓ V) hxx (trCo hf' f b a) with hSdef
  suffices h : lieMat dual d' = lieMat dual d * S by rw [h]; exact hF
  cases dual
  · ext1 i j
    exact congrFun (coord_change (hb V' f' hf' hx') (hb V f hf hx) S h2 (hv' i) (hv i)) j
  · have h3 : d = d' * S.transpose := by
      ext1 i j
      exact congrFun (coord_change (hb V f hf hx) (hb V' f' hf' hx') S.transpose h2 (hv i) (hv' i)) j
    have h4 : d'⁻¹ = S.transpose * d⁻¹ :=
      Matrix.inv_eq_right_inv (by rw [← Matrix.mul_assoc, ← h3, Matrix.mul_nonsing_inv _ hd])
    simp only [lieMat, cond_true]
    rw [h4, Matrix.transpose_mul, Matrix.transpose_transpose]
    rfl

end GlobalTheory.FlagCls

end
