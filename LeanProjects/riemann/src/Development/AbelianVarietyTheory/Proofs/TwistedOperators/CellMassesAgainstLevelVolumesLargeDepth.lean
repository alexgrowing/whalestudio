import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealLineOfPeriodsOnLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefProd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestTupleTermMeasuresDifferByScalarsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingCellMassEqConstMulLocalCoefficientsStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowWt

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem wtAt_big : Big fun ch => ∀ s, WtAt ch s := by
  refine GlobalTheory.RowReal.big_mono ?_ (GlobalTheory.T.rowTest_tupleTerm_measures_differ_by_scalars.and GlobalTheory.T.unfolding_cell_mass_eq_const_mul_local_coefficients)
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch h s ρ μ hH
  obtain ⟨hA, hC⟩ := h
  have hc := hC s ρ μ hH
  classical
  let cf : ℕ → ℂ := fun j => if hj : j ∈ idx D then (hc j hj).choose else 1
  refine ⟨((idx D).map cf).prod, fun t Φ β b hb M M' hM hM' => ?_⟩
  obtain ⟨x, hx, hx1⟩ := hA t Φ β M M' hM hM'
  refine ⟨x, hx, ?_⟩
  have hlt : ∀ j ∈ idx D, 1 ≤ j ∧ j + 2 ≤ D.R.m := fun j hj => by
    rw [idx, List.mem_range'_1] at hj; omega
  have hgf : ∀ j ∈ idx D, b j ∈ GfC _ := fun j hj => by
    obtain ⟨δ, r, -, -, hf⟩ := hb.2 j hj (by have := hlt j hj; omega)
    exact hf.1
  have hfac : ∀ j ∈ idx D, (if h : b j ∈ GfC _ then cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, h⟩ else 0) *
      ((x (.top j) : ℝ) : ℂ) = cf j * (colCoef ch t β j : ℂ) := fun j hj => by
    rw [dif_pos (hgf j hj)]
    have hs := hx (.top j) (show j ≤ D.R.m by have := hlt j hj; omega) (by simp only [ne_eq, Node.top.injEq]; have := hlt j hj; omega)
    have e := (hc j hj).choose_spec t Φ β b hb M M' hM hM' (x (.top j)) hs (hgf j hj)
    simp only [cf, dif_pos hj]
    exact e
  have hsP : sProd D x = ((idx D).map fun j => ((x (.top j) : ℝ) : ℂ)).prod := by
    have h2 : ∏ i ∈ Finset.range (D.R.m + 1), ((x (.grid i D.R.m) : ℝ) : ℂ) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      rw [hx1 (.grid i D.R.m) ⟨by simp at hi; omega, rfl⟩ (by simp) (fun j _ => by simp)]
      simp
    rw [sProd, h2, mul_one, ← List.prod_toFinset _ (show (idx D).Nodup from List.nodup_range')]
    symm
    refine Finset.prod_subset (fun j hj => ?_) (fun j hj0 hj => ?_)
    · rw [List.mem_toFinset] at hj
      have := hlt j hj
      exact Finset.mem_range.2 (by omega)
    · rw [List.mem_toFinset] at hj
      have hj1 := Finset.mem_range.1 hj0
      rw [hx1 (.top j) (show j ≤ D.R.m by omega) (by simp only [ne_eq, Node.top.injEq]; omega) (fun j' hj' e => by cases e; exact hj hj')]
      simp
  have hwt : GlobalTheory.RowVal.wt ρ μ b = ((idx D).map fun j => if h : b j ∈ GfC _ then cellWt (ρ j) (μ j) ((latGrp ch.G j).subgroupOf _) ⟨b j, h⟩
      else 0).prod := by
    unfold GlobalTheory.RowVal.wt
    congr 1
  rw [hwt, hsP, ← List.prod_map_mul, List.map_congr_left hfac, List.prod_map_mul, coef_prod]

end GlobalTheory.RowWt
