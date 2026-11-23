import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualTr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfL
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitSumKernelBallMeasureLeIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitaryKernelLeExpPowEightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantMeasureChartBallOrthonormalLowerBoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
open ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal

namespace GlobalTheory.PoincareL2

theorem nfac_pos' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    {y : Frame X.Ψ r} (hy : y ∈ X.dom) : 0 < X.nfac la y := by
  unfold Data.nfac
  refine Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ?_ _
  exact norm_pos_iff.mpr (div_ne_zero (PoinPf.dmin_ne X hy τ _) (PoinPf.dmin_ne X hy τ _))

theorem poincareNorm_sq_eq_weight_mul_norm_sq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r} (hy : y ∈ X.dom) :
    ENNReal.ofReal (X.pnorm la P y ^ 2) = ENNReal.ofReal (‖P y‖ ^ 2) * IW.Wpsi X la (fun _ => 0) y := by
  have h1 : X.pnorm la P y ^ 2 = ‖P y‖ ^ 2 * Real.exp (-phla X la y) := by
    rw [PoinPf.exp_neg_phla X la (nfac_pos' X la hy)]
    change (‖P y‖ * X.nfac la y) ^ 2 = _
    ring
  have h2 : IW.Wpsi X la (fun _ => 0) y = ENNReal.ofReal (Real.exp (-(phla X la y + 0))) := by
    simp [IW.Wpsi, hy]
  rw [h1, h2, add_zero, ENNReal.ofReal_mul (by positivity)]

theorem sum_le (h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y)) (h2 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8))) (h3 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (Real.exp (-(C * ((X.Ψ.card : ℝ) * r) ^ 8))) ≤ ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r),
      0 < X.p0 → X.p0 < r → IsOrth X x → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → ∀ y ∈ X.dom,
      ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) := by
  obtain ⟨C1, hC1, hS1⟩ := h1
  obtain ⟨C2, hC2, hS2⟩ := h2
  obtain ⟨C3, hC3, hS3⟩ := h3
  refine ⟨C1 + C2 + C3, by positivity, ?_⟩
  intro E _ _ _ r X x hp0 hp0r hx hinj y hy
  have hb := FrameDegreeData.bOf_mem X hy
  have ho : IsOrth X (rmul y (FrameDegreeData.bOf X y)) := FrameDegreeData.ortho_bOf X hy
  set y' := rmul y (FrameDegreeData.bOf X y) with hy'
  have heq : ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) =
      ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y')) := by
    refine tsum_congr fun γ => ?_
    rw [hy', PoinPf.lact_rmul' γ.1 y (FrameDegreeData.bOf X y),
      PoinPf.kaY_rmul X hx ((PairUnfoldPf.lact_mem_dom_iff X γ.2 y).2 hy) hb]
  rw [heq]
  set S := ∑' γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y'))
  set N : ℝ := ((X.Ψ.card : ℝ) * r) ^ 8
  set M := muF X x (Metric.ball (0 : V (nd X)) (1 / (100 * (r : ℝ) ^ 2)) ∩ OmF X x)
  have e1 : M * S ≤ ENNReal.ofReal (Real.exp (C1 * N)) * ENNReal.ofReal (Real.exp (C2 * N)) :=
    (hS1 E r X x y' hp0 hp0r hx ho hinj).trans (mul_le_mul' le_rfl (hS2 E r X y' hp0 hp0r ho))
  have e3 : ENNReal.ofReal (Real.exp (-(C3 * N))) ≤ M := hS3 E r X x hp0 hp0r hx
  have hone : ENNReal.ofReal (Real.exp (C3 * N)) * ENNReal.ofReal (Real.exp (-(C3 * N))) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]; simp
  calc S = (ENNReal.ofReal (Real.exp (C3 * N)) * ENNReal.ofReal (Real.exp (-(C3 * N)))) * S := by
          rw [hone, one_mul]
    _ ≤ (ENNReal.ofReal (Real.exp (C3 * N)) * M) * S := by gcongr
    _ = ENNReal.ofReal (Real.exp (C3 * N)) * (M * S) := by ring
    _ ≤ ENNReal.ofReal (Real.exp (C3 * N)) * (ENNReal.ofReal (Real.exp (C1 * N)) * ENNReal.ofReal (Real.exp (C2 * N))) := by
          gcongr
    _ = ENNReal.ofReal (Real.exp ((C1 + C2 + C3) * N)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add,
            ← Real.exp_add]
          congr 2; ring

end GlobalTheory.PoincareL2

theorem GlobalTheory.PoincareL2.poincare_l2_of_orthogonal (h1 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field
    E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x y
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^
    2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z') b → γ = 1) → ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0
    : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 /
    (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x) * ∑' γ : X.Γ, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.kaY X x (4 *
    (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) (lact γ.1 y)) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ)
    * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X y (4 *
    (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X y)) (h2
    : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (y
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X y → ∫⁻ z, ENNReal.ofReal (ReciprocityTheory.ChartRestriction.G.AR.Up.kaF
    X y (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X
    y) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8))) (h3 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E
    : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x
    : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ENNReal.ofReal (Real.exp
    (-(C * ((X.Ψ.card : ℝ) * r) ^
    8))) ≤ ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x (Metric.ball (0
    : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)) (1 /
    (100 * (r : ℝ) ^ 2)) ∩ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X
    : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x x0 : Frame X.Ψ r) (FF
    : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X))) (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X) → ℂ) (P0
    : Frame X.Ψ r → ℂ), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd
    X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^
    2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x
    z') b → γ = 1) → DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X
    x) → ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 → (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt
    X x z) = F z) → ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la
    (ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P0)
    (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^
    2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (Real.exp (C *
    ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 /
    ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1)
    z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt
    X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) := by
  obtain ⟨C, hC, hsum⟩ := GlobalTheory.PoincareL2.sum_le h1 h2 h3
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ r X la x x0 FF F P0 hp0 hp0r hx hx0 hFF hinj hFd hP0 hPF
  classical
  set bb : ℝ := (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) with hbbdef
  have hInv : IsInvFn X (fun _ : Frame X.Ψ r => (0 : ℝ)) := fun _ _ _ _ _ _ => rfl
  have hW := (IW.metricW_of GlobalTheory.NormFactor.nfacRmul_holds GlobalTheory.NormFactor.nfacLact_holds ortho_holds
    lu_holds X la (fun _ => 0) hInv (fun _ _ => contDiffOn_const) ⟨0, fun _ _ => le_rfl⟩).1
  set W := IW.Wpsi X la (fun _ => 0) with hWdef
  obtain ⟨D⟩ := ExtFPf.luData_of lu_holds X x0 hx0
  set C1 := ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) with hC1def
  have hsumY := hsum E r X x hp0 hp0r hx hinj
  set Pd := X.dom.indicator P0 with hPd
  have hPdm : Measurable Pd := PairUnfoldPf.meas_indC X hP0.1.continuousOn
  set ψ : Frame X.Ψ r → ℝ≥0∞ := fun y => ‖Pd y‖ₑ ^ 2 * W y / ENNReal.ofReal (PoinPf.kaY X x bb y) with hψ
  have hψm : Measurable ψ :=
    ((hPdm.enorm.pow_const 2).mul hW.1).div (PoinPf.meas_kaY X x bb).ennreal_ofReal
  have hψB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y := by
    intro y hy b hb
    have hyb : rmul y b ∈ X.dom := PoinPf.rmulDom X hb hy
    simp only [hψ, hPd, Set.indicator_of_mem hyb, Set.indicator_of_mem hy, hP0.2 y hy b hb,
      hW.2.1 y hy b hb, PoinPf.kaY_rmul X hx hy hb]
    have hpos : 0 < ‖bchar la b‖ ^ 2 := pow_pos (norm_pos_iff.2 (PoinPf.bchar_ne X la hb)) 2
    have h0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
    have ht : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hc : ‖bchar la b‖ₑ ^ 2 = ENNReal.ofReal (‖bchar la b‖ ^ 2) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [enorm_mul, mul_pow, hc]
    congr 1
    rw [ENNReal.div_eq_inv_mul]
    calc ENNReal.ofReal (‖bchar la b‖ ^ 2) * ‖P0 y‖ₑ ^ 2 * ((ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹ * W y)
        = (ENNReal.ofReal (‖bchar la b‖ ^ 2) * (ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹) *
            (‖P0 y‖ₑ ^ 2 * W y) := by ring
      _ = ‖P0 y‖ₑ ^ 2 * W y := by rw [ENNReal.mul_inv_cancel h0 ht, one_mul]
  have hpt : ∀ z ∈ FF, ENNReal.ofReal (X.pnorm la (poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ≤
      C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
    intro z hz
    have hy : ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z ∈ X.dom := hFF.2.1 hz
    rw [GlobalTheory.PoincareL2.poincareNorm_sq_eq_weight_mul_norm_sq X la _ hy]
    have hk0 : ∀ γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) ≠ 0 :=
      fun γ => (ENNReal.ofReal_pos.2 (PoinPf.kaY_pos _ _ _ _)).ne'
    have hkt : ∀ γ : X.Γ, ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) ≠ ⊤ :=
      fun _ => ENNReal.ofReal_ne_top
    have hcs := PoinPf.cs_sq (fun γ : X.Γ => ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ)
      (fun γ => ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))) hk0 hkt
    have e1 : ENNReal.ofReal (‖poin X la P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)‖ ^ 2) ≤
        (∑' γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ) ^ 2 := by
      rw [ENNReal.ofReal_pow (norm_nonneg _)]
      exact pow_le_pow_left₀ zero_le (PoinPf.enorm_poin_le X la P0 _) 2
    have e2 : ∀ γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ ^ 2 /
        ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) =
          ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
      intro γ
      have hγy : lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∈ X.dom := (PairUnfoldPf.lact_mem_dom_iff X γ.2 _).2 hy
      simp only [hψ, hPd, Set.indicator_of_mem hγy, hW.2.2 γ.1 γ.2 _ hy]
      rw [ENNReal.mul_div_right_comm]
    calc ENNReal.ofReal (‖poin X la P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)‖ ^ 2) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)
        ≤ ((∑' γ : X.Γ, ‖P0 (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z))‖ₑ ^ 2 /
            ENNReal.ofReal (PoinPf.kaY X x bb (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))) * C1) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) :=
          mul_le_mul_of_nonneg_right
            (e1.trans (hcs.trans (mul_le_mul_of_nonneg_left (hsumY _ hy) zero_le))) zero_le
      _ = C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) := by
          rw [← tsum_congr e2, ENNReal.tsum_mul_right]; ring
  have hmeasγ : ∀ γ : X.Γ, AEMeasurable (fun z => ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)))
      ((muF X x0).restrict FF) := fun γ =>
    (hψm.comp ((PairUnfoldPf.lact_cont X γ.1).comp (PairUnfoldPf.cpt_cont X x0)).measurable).aemeasurable
  have hunf := PairUnfoldPf.lunfold D FF measInv_holds hx0 hFF ψ hψm hψB
  have hmi := measInv_holds r X x0 x hx0 hx ψ hψm hψB
  have hrhs : ∫⁻ z, ψ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x =
      ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x := by
    refine lintegral_congr_ae ?_
    filter_upwards [ExtFPf.ae_OmF] with z hz
    have hyd : ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom := hz
    simp only [hψ, hPd, Set.indicator_of_mem hyd, hPF z hz, PoinPf.kaY_cpt X hx]
    rw [ENNReal.ofReal_div_of_pos (by unfold kaF; exact Real.exp_pos _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, ENNReal.mul_div_right_comm]
  calc ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂muF X x0
      ≤ ∫⁻ z in FF, C1 * ∑' γ : X.Γ, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) ∂muF X x0 :=
        setLIntegral_mono' hFF.1 hpt
    _ = C1 * ∑' γ : X.Γ, ∫⁻ z in FF, ψ (lact γ.1 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z)) ∂muF X x0 := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_tsum hmeasγ]
    _ = C1 * ∫⁻ z, ψ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ∂muF X x0 := by rw [hunf]
    _ = C1 * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x bb z) * W (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂muF X x := by
        rw [hmi, hrhs]

theorem GlobalTheory.PoincareL2.poincare_l2_inequality : ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (x x0 : Frame X.Ψ r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X))) (F : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X) → ℂ) (P0 : Frame X.Ψ r → ℂ), 0 < X.p0 → X.p0 < r → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ReciprocityTheory.ChartRestriction.G.AR.Up.IsFundSet X x0 FF → (∀ γ ∈ X.Γ, ∀ z z' : ReciprocityTheory.L2DbarEstimates.V (ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X), ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ‖z'‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → ∀ b ∈ Bor X.Ψ r, lact γ (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = rmul (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z') b → γ = 1) → DifferentiableOn ℂ F (ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x) → ReciprocityTheory.ChartRestriction.G.AR.Up.IsBEq X la P0 → (∀ z ∈ ReciprocityTheory.ChartRestriction.G.AR.Up.OmF X x, P0 (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) = F z) → ∫⁻ z in FF, ENNReal.ofReal (X.pnorm la (ReciprocityTheory.ChartRestriction.G.AR.Up.poin X la P0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x0 z) ^ 2) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x0) ≤ ENNReal.ofReal (Real.exp (C * ((X.Ψ.card : ℝ) * r) ^ 8)) * ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / ReciprocityTheory.ChartRestriction.G.AR.Up.kaF X x (4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 + 1) z) * ReciprocityTheory.ChartRestriction.G.AR.Up.IW.Wpsi X la (fun _ => 0) (ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z) ∂(ReciprocityTheory.ChartRestriction.G.AR.Up.muF X x) :=
  GlobalTheory.PoincareL2.poincare_l2_of_orthogonal GlobalTheory.T.orbitSum_kernel_ballMeasure_le_integral GlobalTheory.T.lintegral_unitaryKernel_le_exp_pow_eight GlobalTheory.T.invariantMeasure_chartBall_orthonormal_lower_bound
