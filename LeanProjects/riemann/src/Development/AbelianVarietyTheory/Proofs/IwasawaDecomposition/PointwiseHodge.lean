import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityEqZeroOfWeightedDegreeNeDimStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityUnitAndAboveRankStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CardCmTypeEmbeddingsFixingRootEqHalfFinrankStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactDualLinearFormFlagDegreePointClassStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernDensityLieGramRelationStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.PointHodge

theorem chernTop_add {n : ℕ} {ι : Type} {m : ι → ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n)
    (P Q : MvPolynomial (ι × ℕ) ℝ) : chernTop (P + Q) G v = chernTop P G v + chernTop Q G v := by
  simp only [chernTop, map_add, topCoeff, coeff_add, mul_add, Finset.sum_add_distrib, Complex.add_re]

theorem chernTop_smul {n : ℕ} {ι : Type} {m : ι → ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n)
    (r : ℝ) (P : MvPolynomial (ι × ℕ) ℝ) : chernTop (r • P) G v = r * chernTop P G v := by
  have h : ∀ Q : MvPolynomial (Fin n × Fin n) ℂ, topCoeff (r • Q) = (r : ℂ) * topCoeff Q := fun Q => by
    simp only [topCoeff, coeff_smul, Complex.real_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  simp only [chernTop, map_smul, h, Complex.re_ofReal_mul]
  ring

noncomputable def chernLin {n : ℕ} {ι : Type} {m : ι → ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : MvPolynomial (ι × ℕ) ℝ →ₗ[ℝ] ℝ where
  toFun P := chernTop P G v
  map_add' P Q := chernTop_add G v P Q
  map_smul' r P := chernTop_smul G v r P

theorem pointwise_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), chernTop R (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) = Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ)) * chernTop (pointPoly H Dw) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL la R hR y hy c' hyc A hA
  have hD : (Φ.C k).Y.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by
    rw [Φ.dim_eq k, GlobalTheory.T.card_cmTypeEmbeddingsFixingRoot_eq_half_finrank E H]
  exact GlobalTheory.T.compactDual_linearForm_flagDegree_pointClass E H Dw la R X.dim (Φ.C k).Y.dim (chernLin (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y)) hD hR
    (fun Q d hQ hd => GlobalTheory.T.chernPolyTopDensity_eq_zero_of_weightedDegree_ne_dim _ _ _ _ _ Q d hQ hd) (fun τ Q => (GlobalTheory.T.chernPolyTopDensity_unit_and_above_rank _ _ _ _ _ τ Q).1) (fun τ k Q hk => (GlobalTheory.T.chernPolyTopDensity_unit_and_above_rank _ _ _ _ _ τ Q).2 k hk)
    (fun τ k' Q hk => GlobalTheory.T.hodgeMetric_chernDensity_lieGram_relation E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA τ k' Q hk)

end GlobalTheory.PointHodge
