import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernFormPolyCoeffTopOfNegHermitianSquareStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffProdDetHermitianSquarePowNonneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureBoundedDomainHodgeGStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegHermitianSquareCurvatureOfHolomorphicFrameCStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceHodgeGramLocalHolomorphicModelStatement

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

open scoped ComplexOrder Topology
open GlobalTheory.PointFormSign Matrix
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.PointFormSign

theorem chernTop_pointPoly_nonneg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    {n : ℕ} (G : V n → Mat Dw.mult ℂ) (v : V n)
    (h : ∀ τ : GlobalTheory.AllWt.Psi H, IsNegSq (curv (fun u => G u τ.1) v) (Dw.p + Dw.q - Dw.mult τ.1)) :
    0 ≤ chernTop (pointPoly H Dw) G v := by
  choose S T hS hF using h
  have key : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw) =
      ∏ τ : GlobalTheory.AllWt.Psi H, (sqPoly (T τ)).det ^ (Dw.p + Dw.q - Dw.mult τ.1) := by
    rw [pointPoly, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, map_mul, aeval_C, aeval_X, GlobalTheory.T.chernFormPolyCoeff_top_of_neg_hermitianSquare _ _ _ _ (hS τ) (hF τ)]
    congr 1
    simp only [map_pow, map_neg, map_one]
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  have h0 : 0 ≤ topCoeff (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw)) := by
    rw [key]; exact GlobalTheory.T.topDegreeFormCoeff_prod_det_hermitianSquare_pow_nonneg _ _ _ T
  have hre : 0 ≤ (topCoeff (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => G u x.1) v x.2) (pointPoly H Dw))).re :=
    (Complex.nonneg_iff.1 h0).1
  unfold chernTop
  exact mul_nonneg (inv_nonneg.2 (pow_nonneg Real.pi_pos.le _)) hre

end GlobalTheory.PointFormSign

theorem GlobalTheory.PointFormSign.chernTop_pointPoly_lieGram_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), 0 ≤ chernTop (pointPoly H Dw) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA
  refine GlobalTheory.PointFormSign.chernTop_pointPoly_nonneg H Dw _ _ fun τ => ?_
  obtain ⟨κ, W, Z, hκ, hG, hZ, hW, hWu, hZd⟩ := GlobalTheory.T.lieEigenspaceHodgeGram_local_holomorphic_model E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA τ
  exact GlobalTheory.T.isNegHermitianSquare_curvature_of_holomorphic_frameChange _ _ W Z κ hκ hG hZ hW hWu hZd (GlobalTheory.T.isNegHermitianSquare_curvature_boundedDomainHodgeGram _ _ _ hZd)
