import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DimFormC
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal.PgLe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finrank_F {D : D7} (X : HidaSetting D) : Module.finrank ℚ X.B.I.F = D.R.f := by
  have e1 : Module.finrank ℚ X.B.I.E = Module.finrank ℚ D.host.E :=
    (X.ιE.toRatAlgEquiv).toLinearEquiv.finrank_eq
  have e2 : Module.finrank ℚ X.B.I.F * Module.finrank X.B.I.F X.B.I.E = Module.finrank ℚ X.B.I.E :=
    Module.finrank_mul_finrank ℚ X.B.I.F X.B.I.E
  have e3 : Module.finrank X.B.I.F X.B.I.E = 2 := X.B.I.cm.deg2
  have e4 : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring_nf
  rw [e3] at e2
  omega

theorem one_factor (k b g : ℝ) (f : ℕ) (hk : 1 ≤ k) (hb : 2 ≤ b) (hg : (k * b) ^ 8 ≤ g) (hf : (f : ℝ) ≤ k) :
    (1 + 3 / g) ^ f ≤ Real.exp (1 / 4) := by
  have hk0 : 0 ≤ k := by linarith
  have hkb : 2 * k ≤ k * b := by nlinarith
  have hkb2 : 2 ≤ k * b := by linarith
  have h7 : (2:ℝ) ^ 7 ≤ (k * b) ^ 7 := by gcongr
  have h9 : (k * b) * 2 ^ 7 ≤ (k * b) * (k * b) ^ 7 := mul_le_mul_of_nonneg_left h7 (by linarith)
  have h8 : (k * b) ^ 8 = (k * b) * (k * b) ^ 7 := by ring
  have hg12 : 12 * (f : ℝ) ≤ g := by nlinarith
  have hgpos : 0 < g := by nlinarith
  have hx : 1 + 3 / g ≤ Real.exp (3 / g) := by
    have := Real.add_one_le_exp (3 / g)
    linarith
  have h0 : 0 ≤ 1 + 3 / g := by positivity
  calc (1 + 3 / g) ^ f ≤ Real.exp (3 / g) ^ f := by gcongr
    _ = Real.exp (f * (3 / g)) := (Real.exp_nat_mul _ f).symm
    _ ≤ Real.exp (1 / 4) := by
        apply Real.exp_le_exp.mpr
        have he : (f : ℝ) * (3 / g) = 3 * f / g := by ring
        rw [he, div_le_iff₀ hgpos]
        linarith

theorem exp_quarter_mul_exp_quarter_le_two : Real.exp (1 / 4) * Real.exp (1 / 4) ≤ 2 := by
  rw [← Real.exp_add]
  have h : Real.exp (1 / 4 + 1 / 4) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h1 := Real.exp_one_lt_d9
  have hpos := Real.exp_pos (1 / 4 + 1 / 4)
  nlinarith

theorem pgLeC_of (hS : Formalism.L2.SG.Pf.SatGramLoc.SplitPrimeLoc) (hRC : Formalism.L2.SG.Pf.SatGramLoc.RedCore) : PgLeC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, fun C' Cl _ _ D large₂ X Y hH => ?_⟩
  have hPg := Formalism.L2.SG.Pf.SatGram.tt_eq' hS hRC Y.TR
  unfold Formalism.L2.SG.RowsConc.PgC
  rw [hPg, finrank_F X]
  obtain ⟨⟨hS0, -, -⟩, hP⟩ := hH
  obtain ⟨-, -, -, hfk, -⟩ := hS0
  have hg := hP.2.1
  have hb := Formalism.MainNotions.KappaEndpoints.two_le_scale_b D large₂
  have hk : (1 : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 1 ≤ D.R.k)
  have hf : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast hfk
  have h0 := one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 0 : ℝ) D.R.f hk hb (hg 0).1 hf
  have h1 := one_factor (D.R.k : ℝ) large₂.sc.b (D.host.g 1 : ℝ) D.R.f hk hb (hg 1).1 hf
  calc (1 + 3 / (D.host.g 0 : ℝ)) ^ D.R.f * (1 + 3 / (D.host.g 1 : ℝ)) ^ D.R.f
      ≤ Real.exp (1 / 4) * Real.exp (1 / 4) :=
        mul_le_mul h0 h1 (by positivity) (Real.exp_pos _).le
    _ ≤ 2 := exp_quarter_mul_exp_quarter_le_two

end Formalism.L2.SG.KappaOffDiagonal.PgLe
