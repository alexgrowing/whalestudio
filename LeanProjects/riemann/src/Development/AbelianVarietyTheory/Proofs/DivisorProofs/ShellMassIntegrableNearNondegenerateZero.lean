import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNsqCanonicalAddChartPartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellMass
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.ShellZero

section
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

theorem g_self (A : WeightedAtlas n Y ι La) (la : La) (i : ι) (y : Y)
    (hy : y ∈ (A.chart i).source) : A.g la i i y = 1 := by
  have h := A.g_cocycle la i i i y hy hy hy
  have hg := A.g_ne la i i y hy hy
  exact (mul_eq_left₀ hg).mp h.symm

end

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
private lemma lintegral_nsq_transition_eq_chart_lintegral {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La) (E : La) (i : ι) (c : ℂ) (h : Y → ℝ) (hh : Measurable h)
    (h0 : ∀ y, 0 ≤ h y) (W : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (hW : MeasurableSet W)
    (hWt : W ⊆ (A.chart i).target) :
    ∫⁻ y in (A.chart i).source ∩ A.chart i ⁻¹' W,
        ENNReal.ofReal (A.nsq (A.kap + E) (fun j y => A.g (A.kap + E) j i y * c) y * h y) ∂A.mu =
      ∫⁻ v in W, ENNReal.ofReal (‖c‖ ^ 2 * h ((A.chart i).symm v) *
        Real.exp (-A.ph E i ((A.chart i).symm v))) := by
  classical
  set D : ι → Y → ℂ := fun j y => A.g (A.kap + E) j i y * (c * (Real.sqrt (h y) : ℂ)) with hD
  have hsq : ∀ y, (‖(Real.sqrt (h y) : ℂ)‖) ^ 2 = h y := by
    intro y
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (h0 y)]
  have hL : ∀ y, A.nsq (A.kap + E) (fun j y => A.g (A.kap + E) j i y * c) y * h y =
      A.nsq (A.kap + E) D y := by
    intro y
    simp only [_root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq, hD, norm_mul, mul_pow, hsq]
    ring
  simp_rw [hL]
  rw [_root_.GlobalTheory.OTY.lintegral_nsq_chart_part n Y ι La A E i W D hW hWt]
  · refine setLIntegral_congr_fun hW (fun v hv => ?_)
    have hs : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target (hWt hv)
    simp only [hD, A.g_self _ i hs, one_mul, norm_mul, mul_pow, hsq]
  · intro y hy _
    simp only [hD, A.g_self _ i hy, one_mul]
  · have hc : ContinuousOn (A.chart i).symm W :=
      (A.chart i).continuousOn_symm.mono hWt
    have hm : AEMeasurable (fun v => c * (Real.sqrt (h ((A.chart i).symm v)) : ℂ))
        (volume.restrict W) :=
      (aemeasurable_const.mul (Complex.measurable_ofReal.comp_aemeasurable
        ((Real.continuous_sqrt.measurable.comp hh).comp_aemeasurable (hc.aemeasurable hW))))
    refine hm.congr ?_
    filter_upwards [ae_restrict_mem hW] with v hv
    have hs : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target (hWt hv)
    simp only [Function.comp, hD, A.g_self _ i hs, one_mul]

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in

theorem _root_.GlobalTheory.OTY.ShellZero.shell_near_zero : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), 1 ≤ n → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ P ∈ A.zeroSet s, _root_.GlobalTheory.Published.L2Extension.jacAt A s P ≠ 0 → ∀ (c : ℂ) (δ : ℝ), 0 < δ → ∃ N : Set Y, IsOpen N ∧ P ∈ N ∧ N ⊆ (A.chart (A.pick P)).source ∧ (∀ T : ℝ, 2 ≤ T → ∫⁻ y in N ∩ {y | -T - 1 ≤ δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y ∧ δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y ≤ -T + 1}, ENNReal.ofReal (A.nsq (A.kap + E) (fun i y => A.g (A.kap + E) i (A.pick P) y * c) y * Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)) ∂A.mu ≤ ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ * _root_.GlobalTheory.Published.L2Extension.resSq A E L s P c)) ∧ ∫⁻ y in N, ENNReal.ofReal (1 / (1 + (δ * _root_.GlobalTheory.Published.L2Extension.psi A L s y) ^ 2) * A.nsq (A.kap + E) (fun i y => A.g (A.kap + E) i (A.pick P) y * c) y * Real.exp (-_root_.GlobalTheory.Published.L2Extension.psi A L s y)) ∂A.mu < ⊤ := by
  intro n Y _ _ _ _ _ ι La _ A hn E L s hs P hP hJ c δ hδ
  set i := A.pick P with hi
  set e := A.chart i with he
  set Z : _root_.ReciprocityTheory.L2DbarEstimates.V n → _root_.ReciprocityTheory.L2DbarEstimates.V n := A.zLoc (fun _ _ => 1) s i with hZ
  set lam : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ := fun v => A.ph L i (e.symm v) with hlam
  set φ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ := fun v => A.ph E i (e.symm v) with hφ
  set ψ : Y → ℝ := _root_.GlobalTheory.Published.L2Extension.psi A L s with hψdef
  have hPs : P ∈ e.source := A.mem_pick P
  have hp : e P ∈ e.target := e.map_source hPs
  have hZd : DifferentiableOn ℂ Z e.target := by
    have hk : ∀ k, DifferentiableOn ℂ (fun v => s k i (e.symm v) / 1) e.target := by
      intro k
      have := ((hs k).1 i)
      simpa [Set.preimage_univ, Set.inter_univ, Function.comp_def] using this
    have : DifferentiableOn ℂ (fun v => (EuclideanSpace.equiv (Fin n) ℂ).symm
        (fun k => s k i (e.symm v) / 1)) e.target :=
      (EuclideanSpace.equiv (Fin n) ℂ).symm.differentiable.comp_differentiableOn
        (differentiableOn_pi.2 hk)
    exact this
  have hZ0 : Z (e P) = 0 := by
    simp only [hZ, _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc, he]
    rw [(A.chart i).left_inv hPs]
    have hPk : ∀ k, s k i P = 0 := hP
    have h0 : (fun k => s k i P / 1) = 0 := funext fun k => by simp [hPk k]
    rw [h0]
    rfl
  have hdet : (fderiv ℂ Z (e P)).det ≠ 0 := hJ
  have hlamc : ContinuousOn lam e.target :=
    (A.continuousOn_ph L i).comp e.continuousOn_symm (fun v hv => e.map_target hv)
  have hφc : ContinuousOn φ e.target :=
    (A.continuousOn_ph E i).comp e.continuousOn_symm (fun v hv => e.map_target hv)
  have hψx : ∀ x ∈ e.source, ψ x = n * Real.log (‖Z (e x)‖ ^ 2 * Real.exp (-lam (e x))) := by
    intro x hx
    have h1 := A.sqn_s_eq (w0 := fun _ _ => (1 : ℂ)) hs hx one_ne_zero
    simp only [hψdef, _root_.GlobalTheory.Published.L2Extension.psi, h1, hlam, e.left_inv hx, hZ]
    rw [norm_one, one_pow, one_mul, mul_comm (Real.exp _)]
  have hψm : Measurable ψ := by
    simp only [hψdef, _root_.GlobalTheory.Published.L2Extension.psi]
    exact measurable_const.mul (Real.measurable_log.comp (A.continuous_sqn hs).measurable)
  obtain ⟨ρ, hρ, hball, hshell⟩ := _root_.GlobalTheory.ShellMass.shell_mass n hn (e P) e.target Z lam e.open_target hp hZd hZ0
    hdet hlamc φ (2 / δ) (1 / 30) hφc (by positivity) (by norm_num)
  set W : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n) := ball (e P) (ρ / 2) with hW
  have hWm : MeasurableSet W := measurableSet_ball
  have hWρ : W ⊆ ball (e P) ρ := ball_subset_ball (by linarith)
  have hWt : W ⊆ e.target := hWρ.trans hball
  set D : ι → Y → ℂ := fun j y => A.g (A.kap + E) j i y * c with hD
  have hψW : ∀ v ∈ W, ψ (e.symm v) = n * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v)) := by
    intro v hv
    rw [hψx _ (e.map_target (hWt hv)), e.right_inv (hWt hv)]
  refine ⟨e.source ∩ e ⁻¹' W, e.isOpen_inter_preimage isOpen_ball, ⟨hPs, mem_ball_self (by positivity)⟩,
    Set.inter_subset_left, ?_⟩
  have hpart1 : ∀ T : ℝ, 2 ≤ T → ∫⁻ y in (e.source ∩ e ⁻¹' W) ∩
      {y | -T - 1 ≤ δ * ψ y ∧ δ * ψ y ≤ -T + 1},
      ENNReal.ofReal (A.nsq (A.kap + E) D y * Real.exp (-ψ y)) ∂A.mu ≤
      ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ *
        _root_.GlobalTheory.Published.L2Extension.resSq A E L s P c) := by
    intro T hT
    set S : Set Y := {y | -T - 1 ≤ δ * ψ y ∧ δ * ψ y ≤ -T + 1} with hS
    have hSm : MeasurableSet S :=
      (measurableSet_le measurable_const (measurable_const.mul hψm)).inter
        (measurableSet_le (measurable_const.mul hψm) measurable_const)
    set h : Y → ℝ := S.indicator (fun y => Real.exp (-ψ y)) with hh
    have hhm : Measurable h := (Real.measurable_exp.comp hψm.neg).indicator hSm
    have h0 : ∀ y, 0 ≤ h y := fun y => Set.indicator_nonneg (fun y _ => (Real.exp_pos _).le) y
    have hLHS : ∫⁻ y in (e.source ∩ e ⁻¹' W) ∩ S,
        ENNReal.ofReal (A.nsq (A.kap + E) D y * Real.exp (-ψ y)) ∂A.mu =
        ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal (A.nsq (A.kap + E) D y * h y) ∂A.mu := by
      rw [Set.inter_comm, ← Measure.restrict_restrict hSm, ← lintegral_indicator hSm]
      refine lintegral_congr fun y => ?_
      by_cases hy : y ∈ S
      · simp only [Set.indicator_of_mem hy, hh]
      · simp only [Set.indicator_of_notMem hy, hh, mul_zero, ENNReal.ofReal_zero]
    rw [hLHS]
    refine (lintegral_nsq_transition_eq_chart_lintegral A E i c h hhm h0 W hWm hWt).trans_le ?_
    set Ψ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ := fun v => n * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v)) with hΨ
    set b : ℝ := (1 - T) / δ with hb
    set S' : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n) := {v | Z v ≠ 0 ∧ b - 2 / δ ≤ Ψ v ∧ Ψ v ≤ b} with hS'
    set G : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp (-φ v) * Real.exp (-Ψ v)) with hG
    have hpt : ∀ v ∈ W, ENNReal.ofReal (‖c‖ ^ 2 * h (e.symm v) * Real.exp (-A.ph E i (e.symm v))) ≤
        ENNReal.ofReal (‖c‖ ^ 2) * S'.indicator G v := by
      intro v hv
      by_cases hx : e.symm v ∈ S
      · have hψv := hψW v hv
        have h1 : δ * Ψ v ≤ -T + 1 := by
          have := hx.2
          rw [hψv] at this
          exact this
        have h2 : -T - 1 ≤ δ * Ψ v := by
          have := hx.1
          rw [hψv] at this
          exact this
        have hZv : Z v ≠ 0 := by
          intro hz
          have : Ψ v = 0 := by simp [hΨ, hz]
          rw [this, mul_zero] at h1
          linarith
        have hmem : v ∈ S' := by
          refine ⟨hZv, ?_, ?_⟩
          · rw [hb, div_sub_div_same, div_le_iff₀ hδ]
            linarith
          · rw [hb, le_div_iff₀ hδ]
            linarith
        rw [Set.indicator_of_mem hmem, hG, ← ENNReal.ofReal_mul (sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
        simp only [hh, Set.indicator_of_mem hx, hψv, hφ]
        ring
      · simp only [hh, Set.indicator_of_notMem hx, mul_zero, zero_mul, ENNReal.ofReal_zero]
        exact bot_le
    calc _ ≤ ∫⁻ v in W, ENNReal.ofReal (‖c‖ ^ 2) * S'.indicator G v := setLIntegral_mono' hWm hpt
      _ = ENNReal.ofReal (‖c‖ ^ 2) * ∫⁻ v in W, S'.indicator G v :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (‖c‖ ^ 2) * ∫⁻ v in ball (e P) ρ ∩ S', G v := by
          gcongr ENNReal.ofReal (‖c‖ ^ 2) * ?_
          calc ∫⁻ v in W, S'.indicator G v ≤ ∫⁻ v in S', G v ∂(volume.restrict W) :=
                lintegral_indicator_le _ _
            _ = ∫⁻ v in S' ∩ W, G v := by rw [Measure.restrict_restrict' hWm]
            _ ≤ ∫⁻ v in ball (e P) ρ ∩ S', G v :=
                lintegral_mono_set fun v hv => ⟨hWρ hv.2, hv.1⟩
      _ ≤ ENNReal.ofReal (‖c‖ ^ 2) * ENNReal.ofReal ((1 + 1 / 30) *
            (Real.pi ^ n / ((n - 1).factorial : ℝ) * (2 / δ / n)) *
            (Real.exp (-φ (e P) + n * lam (e P)) / ‖(fderiv ℂ Z (e P)).det‖ ^ 2)) := by
          gcongr ENNReal.ofReal (‖c‖ ^ 2) * ?_
          exact hshell b
      _ ≤ _ := by
          rw [← ENNReal.ofReal_mul (sq_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hJeq : _root_.GlobalTheory.Published.L2Extension.jacAt A s P = (fderiv ℂ Z (e P)).det := rfl
          have hφP : φ (e P) = A.ph E i P := by simp only [hφ, e.left_inv hPs]
          have hlamP : lam (e P) = A.ph L i P := by simp only [hlam, e.left_inv hPs]
          have hres : _root_.GlobalTheory.Published.L2Extension.resSq A E L s P c = ‖c‖ ^ 2 /
              ‖(fderiv ℂ Z (e P)).det‖ ^ 2 * Real.exp (-A.ph E i P + n * A.ph L i P) := by
            unfold _root_.GlobalTheory.Published.L2Extension.resSq
            rw [hJeq, norm_div, div_pow]
          rw [hres, hφP, hlamP]
          have hJ0 : ‖(fderiv ℂ Z (e P)).det‖ ≠ 0 := norm_ne_zero_iff.mpr hdet
          have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
          set K := Real.pi ^ n / ((n - 1).factorial : ℝ) with hK
          set X := Real.exp (-A.ph E i P + n * A.ph L i P) with hX
          set J := ‖(fderiv ℂ Z (e P)).det‖ with hJdef
          have hK0 : 0 ≤ K := by positivity
          have hX0 : 0 ≤ X := (Real.exp_pos _).le
          have key : ‖c‖ ^ 2 * ((1 + 1 / 30) * (K * (2 / δ / n)) * (X / J ^ 2)) =
              62 / 30 * K / δ * (‖c‖ ^ 2 / J ^ 2 * X) * (1 / n) := by
            field_simp
            ring
          rw [key]
          refine mul_le_of_le_one_right (by positivity) ?_
          rw [div_le_one hnpos]
          exact_mod_cast hn
  refine ⟨hpart1, ?_⟩
  set N : Set Y := e.source ∩ e ⁻¹' W with hN
  have hNm : MeasurableSet N := (e.isOpen_inter_preimage isOpen_ball).measurableSet
  set Kc : ℝ≥0∞ := ENNReal.ofReal (62 / 30 * (Real.pi ^ n / ((n - 1).factorial : ℝ)) / δ *
        _root_.GlobalTheory.Published.L2Extension.resSq A E L s P c) with hKc
  set F : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (1 / (1 + (δ * ψ y) ^ 2) *
      A.nsq (A.kap + E) D y * Real.exp (-ψ y)) with hF
  set w : ℕ → ℝ := fun m => 1 / (1 + ((m : ℝ) + 1) ^ 2) with hw
  set Sh : ℕ → Set Y := fun m => N ∩ {y | -((m : ℝ) + 2) - 1 ≤ δ * ψ y ∧
      δ * ψ y ≤ -((m : ℝ) + 2) + 1} with hSh
  set Hi : Set Y := N ∩ {y | -1 ≤ δ * ψ y} with hHi
  have hnsq : ∀ y, 0 ≤ A.nsq (A.kap + E) D y * Real.exp (-ψ y) :=
    fun y => mul_nonneg (A.nsq_nonneg _ _ _) (Real.exp_pos _).le

  have hshellF : ∀ m : ℕ, ∫⁻ y in Sh m, F y ∂A.mu ≤ ENNReal.ofReal (w m) * Kc := by
    intro m
    have hShm : MeasurableSet (Sh m) := hNm.inter
      ((measurableSet_le measurable_const (measurable_const.mul hψm)).inter
        (measurableSet_le (measurable_const.mul hψm) measurable_const))
    calc ∫⁻ y in Sh m, F y ∂A.mu ≤ ∫⁻ y in Sh m, ENNReal.ofReal (w m) *
          ENNReal.ofReal (A.nsq (A.kap + E) D y * Real.exp (-ψ y)) ∂A.mu := by
          refine setLIntegral_mono' hShm fun y hy => ?_
          have hy2 := hy.2.2
          have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          have hsq : ((m : ℝ) + 1) ^ 2 ≤ (δ * ψ y) ^ 2 := by nlinarith
          have hwle : 1 / (1 + (δ * ψ y) ^ 2) ≤ w m :=
            one_div_le_one_div_of_le (by positivity) (by linarith)
          rw [hF, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right hwle (hnsq y)
      _ = ENNReal.ofReal (w m) * ∫⁻ y in Sh m,
          ENNReal.ofReal (A.nsq (A.kap + E) D y * Real.exp (-ψ y)) ∂A.mu :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (w m) * Kc := by
          gcongr ENNReal.ofReal (w m) * ?_
          exact hpart1 ((m : ℝ) + 2) (by have := Nat.cast_nonneg (α := ℝ) m; linarith)

  have hHiF : ∫⁻ y in Hi, F y ∂A.mu < ⊤ := by
    have hHim : MeasurableSet Hi := hNm.inter (measurableSet_le measurable_const
      (measurable_const.mul hψm))
    obtain ⟨C, hC⟩ := (isCompact_closedBall (e P) (ρ / 2)).exists_bound_of_continuousOn
      (hφc.mono ((closedBall_subset_ball (by linarith)).trans hball))
    calc ∫⁻ y in Hi, F y ∂A.mu ≤ ∫⁻ y in Hi, ENNReal.ofReal
          (A.nsq (A.kap + E) D y * (fun _ => Real.exp (1 / δ)) y) ∂A.mu := by
          refine setLIntegral_mono' hHim fun y hy => ?_
          have hy2 : -1 ≤ δ * ψ y := hy.2
          have hexp : Real.exp (-ψ y) ≤ Real.exp (1 / δ) := by
            refine Real.exp_le_exp.mpr ?_
            rw [le_div_iff₀ hδ]
            linarith
          have hw1 : 1 / (1 + (δ * ψ y) ^ 2) ≤ 1 := by
            rw [div_le_one (by positivity)]
            nlinarith
          refine ENNReal.ofReal_le_ofReal ?_
          calc 1 / (1 + (δ * ψ y) ^ 2) * A.nsq (A.kap + E) D y * Real.exp (-ψ y)
              ≤ 1 * A.nsq (A.kap + E) D y * Real.exp (-ψ y) := by
                gcongr
                exact A.nsq_nonneg _ _ _
            _ ≤ A.nsq (A.kap + E) D y * Real.exp (1 / δ) := by
                rw [one_mul]
                exact mul_le_mul_of_nonneg_left hexp (A.nsq_nonneg _ _ _)
      _ ≤ ∫⁻ y in N, ENNReal.ofReal
          (A.nsq (A.kap + E) D y * (fun _ => Real.exp (1 / δ)) y) ∂A.mu :=
          lintegral_mono_set Set.inter_subset_left
      _ = ∫⁻ v in W, ENNReal.ofReal (‖c‖ ^ 2 * Real.exp (1 / δ) *
          Real.exp (-A.ph E i (e.symm v))) :=
          lintegral_nsq_transition_eq_chart_lintegral A E i c (fun _ => Real.exp (1 / δ)) measurable_const
            (fun _ => (Real.exp_pos _).le) W hWm hWt
      _ ≤ ∫⁻ v in W, ENNReal.ofReal (‖c‖ ^ 2 * Real.exp (1 / δ) * Real.exp C) := by
          refine setLIntegral_mono' hWm fun v hv => ENNReal.ofReal_le_ofReal ?_
          have hv' : v ∈ closedBall (e P) (ρ / 2) := ball_subset_closedBall hv
          have hCv : -φ v ≤ C := (neg_le_abs _).trans (hC v hv')
          gcongr
      _ < ⊤ := by
          rw [setLIntegral_const]
          exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

  have hcover : N ⊆ Hi ∪ ⋃ m : ℕ, Sh m := by
    intro y hy
    by_cases h1 : -1 ≤ δ * ψ y
    · exact Or.inl ⟨hy, h1⟩
    · right
      push_neg at h1
      set t := -(δ * ψ y) with ht
      have ht1 : 1 ≤ t := by linarith
      have hfl : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht1)
      have hfle : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
      have hlt : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
      refine Set.mem_iUnion.mpr ⟨⌊t⌋₊ - 1, hy, ?_, ?_⟩
      · rw [Nat.cast_sub hfl]
        push_cast
        linarith
      · rw [Nat.cast_sub hfl]
        push_cast
        linarith
  have hsum : Summable w := by
    have h2 : Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
      have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
      simpa [Nat.cast_add, Nat.cast_one] using this
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) h2
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  calc ∫⁻ y in N, F y ∂A.mu ≤ ∫⁻ y in Hi ∪ ⋃ m : ℕ, Sh m, F y ∂A.mu := lintegral_mono_set hcover
    _ ≤ ∫⁻ y in Hi, F y ∂A.mu + ∫⁻ y in ⋃ m : ℕ, Sh m, F y ∂A.mu := lintegral_union_le _ _ _
    _ ≤ ∫⁻ y in Hi, F y ∂A.mu + ∑' m : ℕ, ENNReal.ofReal (w m) * Kc := by
        gcongr
        exact (lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum hshellF)
    _ < ⊤ := by
        rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum]
        exact ENNReal.add_lt_top.mpr ⟨hHiF, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ENNReal.ofReal_lt_top⟩

end GlobalTheory.OTY.ShellZero
