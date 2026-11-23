import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicFrobeniusPointComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointPeriodRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinatorialTangentPointConditionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PAdicPointTangentMapFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEigenvectorHeightMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLatticeBasisOfEigenvectorsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

namespace GlobalTheory.DetHT

theorem pointSt_of : BridgeSt → EigSt → CovolSt → PointSt := by
  intro hB hE hC E _ _ _ _ H Dw τ p _
  obtain ⟨δ, hδ, hEδ⟩ := hE E H p
  refine ⟨-(Dw.mult τ.1 : ℝ) * Real.log ‖δ‖, ?_⟩
  intro l Xo c Z _ f hf P y z yb hyP Q π ψ hPt hHT hfy
  letI := H.starRing
  obtain ⟨g, a, x, hchg, -, -, htie, hlat⟩ := hHT
  have hPy : P.x = y.x := by rw [← Descent.ptF_fst P, ← hyP, Descent.ptF_fst]
  have hzy : z.x = y.x := hchg.1.symm
  have hzP : ptF z = ptF P := by
    refine pullback.hom_ext ?_ ?_
    · rw [Descent.ptF_fst, Descent.ptF_fst, hzy, hPy]
    · rw [Descent.ptF_snd, Descent.ptF_snd]
  have LT := fun σ j => GlobalTheory.T.p_adic_frobenius_point_comparison E H Dw l Xo c Z p P z yb hzP Q π ψ hPt σ j (x σ j) (htie σ j)
  have LE := fun σ j => GlobalTheory.T.p_adic_point_period_relation E H Dw l Xo c Z p z yb (ptF P) Q π ψ hPt σ j (x σ j) (htie σ j)
  have uY := fun σ => GlobalTheory.T.combinatorial_tangent_point_condition E H Dw l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Z ℂ_[p] y σ
  set vY := (frameOf Z y).v with hvY
  set vZ := (frameOf Z z).v with hvZ
  have tY : ∀ σ k, IsTanAtG Z.t (ptF y ≫ Z.j) (vY σ k) := (frameOf Z y).tan
  have rY : ∀ σ k, TanRel Z (ptF y) (y.u σ k) (vY σ k) := (tie_frameOf Z y).2.2
  have tZ : ∀ σ k, IsTanAtG Z.t (ptF z ≫ Z.j) (vZ σ k) := (frameOf Z z).tan
  have rZ : ∀ σ k, TanRel Z (ptF z) (z.u σ k) (vZ σ k) := (tie_frameOf Z z).2.2
  clear_value vY vZ
  rw [hyP] at tY rY uY
  rw [hzP] at tZ rZ
  have Cz : ∀ σ i, IsCombAtG Z.t (ptF P ≫ Z.j) (vZ σ) (g σ i) (vY σ i) := fun σ i =>
    (TanRel.comb_iff ((Descent.ptF_fst P).trans (hPy.trans hzy.symm)) rfl (rZ σ) (rY σ i) _).1 (hchg.2.1 σ i)
  obtain ⟨G, b, hGu, hG⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c ℂ_[p] y P).1 hPy
  have Cy : ∀ σ i, IsCombAtG Z.t (ptF P ≫ Z.j) (vY σ) (G σ i) ((frameOf Z P).v σ i) := fun σ i =>
    (TanRel.comb_iff ((Descent.ptF_fst P).trans hPy) rfl (rY σ) ((tie_frameOf Z P).2.2 σ i) _).1 (hG.2.1 σ i)
  have hev := GlobalTheory.FlatGL.evR_flat_chg τ hf P y hPy (G τ.1) (G (conjEmb τ.1)) (hG.2.1 τ.1) (hG.2.1 _)
  have hL := fun σ => GlobalTheory.T.p_adic_point_tangent_map_formula hB E H Dw l Xo c Z p (ptF P) yb Q π ψ hPt (Dw.mult σ) (x σ) (vZ σ) (vY σ) (g σ)
    (tZ σ) (LT σ) (Cz σ)
  have h1 := hC E H Z.X Z.t ℂ_[p] (ptF P ≫ Z.j) (GlobalTheory.ShFam.Pad.latHT Z.t p (ptF P ≫ Z.j)) (Dw.mult τ.1)
    ((frameOf Z P).v τ.1) (vY τ.1) (G τ.1) δ⁻¹ (inv_ne_zero hδ) (tY τ.1) (uY τ.1)
    (fun a w hw => (hL τ.1 a w hw).trans (GlobalTheory.T.lattice_eigenvector_height_matrix E H p δ hδ l c Q τ (hEδ l c Q τ) _ (x τ.1) (g τ.1)
      (LE τ.1) (hlat τ.1) a)) (Cy τ.1) (hGu τ.1).ne_zero
  have h2 := hC E H Z.X Z.t ℂ_[p] (ptF P ≫ Z.j) (GlobalTheory.ShFam.Pad.latHT Z.t p (ptF P ≫ Z.j)) (Dw.mult (conjEmb τ.1))
    ((frameOf Z P).v (conjEmb τ.1)) (vY (conjEmb τ.1)) (G (conjEmb τ.1)) 1 one_ne_zero (tY _) (uY _)
    (fun a w hw => (hL _ a w hw).trans (GlobalTheory.T.height_lattice_basis_of_eigenvectors E H p l c Q τ _ (x (conjEmb τ.1)) (g (conjEmb τ.1))
      (LE _) (hlat _) a)) (Cy _) (hGu _).ne_zero
  have d1 := (hGu τ.1).ne_zero
  have d2 := (hGu (conjEmb τ.1)).ne_zero
  have hP0 : evR Xo c f P ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hev
    exact mul_ne_zero d2 hfy hev.symm
  refine ⟨hP0, ?_⟩
  have e := congrArg (fun t => Real.log ‖t‖) hev
  simp only [norm_mul] at e
  rw [Real.log_mul (norm_ne_zero_iff.2 hP0) (norm_ne_zero_iff.2 d1),
    Real.log_mul (norm_ne_zero_iff.2 d2) (norm_ne_zero_iff.2 hfy)] at e
  unfold lnDet
  rw [h1, h2, norm_inv, Real.log_inv, norm_one, Real.log_one]
  linarith

end GlobalTheory.DetHT
