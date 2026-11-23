import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMetricRatioDifferentiableChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMetricRatioDifferentiableNonnegStatement

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo
open GlobalTheory.ChartGlue Topology Filter

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GradFlag

theorem transfer {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {σ : k →+* ℂ} {d : ℕ}
    {R : GlobalTheory.AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) (f : GlobalTheory.CxPts p σ → ℝ)
    (ch ch₀ : GlobalTheory.AlgChart p σ d) {y : GlobalTheory.CxPts p σ} (hy : y ∈ ch.e.source) (hy₀ : y ∈ ch₀.e.source)
    (hd : DifferentiableAt ℝ (f ∘ ch₀.e.symm) (ch₀.e y)) (B : ℝ)
    (hb : ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, |fderiv ℝ (f ∘ ch₀.e.symm) (ch₀.e y) ξ| ≤ B * √(a ch₀ y ξ.ofLp)) :
    DifferentiableAt ℝ (f ∘ ch.e.symm) (ch.e y) ∧
      ∀ ξ : ReciprocityTheory.L2DbarEstimates.V d, |fderiv ℝ (f ∘ ch.e.symm) (ch.e y) ξ| ≤ B * √(a ch y ξ.ofLp) := by
  have ho := isOpen_over ch.e ch₀.e.open_source
  have hn := ho.mem_nhds (mem_over ch.e hy hy₀)
  have hT : DifferentiableAt ℂ (ch₀.e ∘ ch.e.symm) (ch.e y) := (ch.holo_trans ch₀).differentiableAt hn
  have e0 : (ch₀.e ∘ ch.e.symm) (ch.e y) = ch₀.e y := congrArg ch₀.e (ch.e.left_inv hy)
  have hd' : DifferentiableAt ℝ (f ∘ ch₀.e.symm) ((ch₀.e ∘ ch.e.symm) (ch.e y)) := e0 ▸ hd
  have heq : f ∘ ch.e.symm =ᶠ[𝓝 (ch.e y)] (f ∘ ch₀.e.symm) ∘ (ch₀.e ∘ ch.e.symm) :=
    Filter.eventually_of_mem hn fun v hv => by simp only [Function.comp_apply, ch₀.e.left_inv hv.2]
  have hc := hd'.hasFDerivAt.comp (ch.e y) (hT.restrictScalars ℝ).hasFDerivAt
  refine ⟨(hc.differentiableAt).congr_of_eventuallyEq heq, fun ξ => ?_⟩
  rw [heq.fderiv_eq, hc.fderiv, ha.trans hy hy₀ ξ.ofLp]
  have e1 : (fderiv ℝ (ch₀.e ∘ ch.e.symm) (ch.e y)) ξ = WithLp.toLp 2 (ch.dtrans ch₀ y ξ.ofLp) := by
    rw [hT.fderiv_restrictScalars ℝ]
    rfl
  simp only [ContinuousLinearMap.comp_apply, e1]
  rw [e0]
  exact hb _

def GradLineInt : Prop := Hypotheses2 → HypothesesH → OnCore fun D O x P => ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (ρ : DV.Rt D.what₂.Tau O.N)
  (y₀ : GlobalTheory.CxPts (O.var c).str σ), y₀ ∈ offBd O.Φ c σ →
  ∃ (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (GlobalTheory.CxPts (O.var c).str σ)) (C : ℝ),
    IsOpen U ∧ y₀ ∈ U ∧ U ⊆ ch.e.source ∧ ∀ y ∈ U, y ∈ offBd O.Φ c σ ∧
      DifferentiableAt ℝ (lnRatio (metsOf x O.Φ c none σ (O.ex ρ)) (refMet x O.Φ c σ (O.ex ρ)) ∘ ch.e.symm) (ch.e y) ∧
      ∀ ξ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim,
        |fderiv ℝ (lnRatio (metsOf x O.Φ c none σ (O.ex ρ)) (refMet x O.Φ c σ (O.ex ρ)) ∘ ch.e.symm) (ch.e y) ξ| ≤
          C * √(P.om c σ ch y ξ.ofLp)

def GradLineBd : Prop := Hypotheses2 → HypothesesH → OnCore fun D O x P => ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (ρ : DV.Rt D.what₂.Tau O.N)
  (y₀ : GlobalTheory.CxPts (O.var c).str σ), y₀ ∉ offBd O.Φ c σ →
  ∃ (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (GlobalTheory.CxPts (O.var c).str σ)) (C μ : ℝ),
    IsOpen U ∧ y₀ ∈ U ∧ U ⊆ ch.e.source ∧ 0 ≤ μ ∧ ∀ y ∈ U, y ∈ offBd O.Φ c σ →
      DifferentiableAt ℝ (lnRatio (metsOf x O.Φ c none σ (O.ex ρ)) (refMet x O.Φ c σ (O.ex ρ)) ∘ ch.e.symm) (ch.e y) ∧
      ∀ ξ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim,
        |fderiv ℝ (lnRatio (metsOf x O.Φ c none σ (O.ex ρ)) (refMet x O.Φ c σ (O.ex ρ)) ∘ ch.e.symm) (ch.e y) ξ| ≤
          C * O.met.r c σ y ^ μ * Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp)

abbrev lineFn {D : D7} (O : Setup D) (x : ToroidalCompactificationData O.s) (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (ρ : DV.Rt D.what₂.Tau O.N) :
    GlobalTheory.CxPts (O.var c).str σ → ℝ :=
  lnRatio (metsOf x O.Φ c none σ (O.ex ρ)) (refMet x O.Φ c σ (O.ex ρ))

theorem gradSt_of_local (hI : GradLineInt) (hB : GradLineBd) : Hypotheses2 → HypothesesH → GradSt := by
  intro h2 hH D O x P hc hN hR
  have hI' := hI h2 hH D O x P hc hN hR
  have hB' := hB h2 hH D O x P hc hN hR
  have hr1 : ∀ c σ (y : GlobalTheory.CxPts (O.var c).str σ), 1 ≤ O.met.r c σ y := fun c σ y => by
    rw [hc.r_eq]
    exact (by linarith [Real.add_one_le_exp (1 : ℝ)] : (1 : ℝ) ≤ Real.exp 1).trans exp_le_rFlag
  have hE : ∀ c σ (y : GlobalTheory.CxPts (O.var c).str σ) (a : ℝ), 0 ≤ Real.exp (O.met.r c σ y / 2) * √a :=
    fun _ _ _ _ => mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)

  have loc : ∀ c σ (ρ : DV.Rt D.what₂.Tau O.N) (y₀ : GlobalTheory.CxPts (O.var c).str σ),
      ∃ (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (GlobalTheory.CxPts (O.var c).str σ)) (C μ : ℝ),
        IsOpen U ∧ y₀ ∈ U ∧ U ⊆ ch.e.source ∧ 0 ≤ C ∧ 0 ≤ μ ∧ ∀ y ∈ U, y ∈ offBd O.Φ c σ →
          DifferentiableAt ℝ (lineFn O x c σ ρ ∘ ch.e.symm) (ch.e y) ∧
          ∀ ξ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim, |fderiv ℝ (lineFn O x c σ ρ ∘ ch.e.symm) (ch.e y) ξ| ≤
            C * O.met.r c σ y ^ μ * Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp) := by
    intro c σ ρ y₀
    by_cases h₀ : y₀ ∈ offBd O.Φ c σ
    · obtain ⟨ch, U, C, hUo, hy₀, hUs, hb⟩ := hI' c σ ρ y₀ h₀
      refine ⟨ch, U, max C 0, 0, hUo, hy₀, hUs, le_max_right _ _, le_rfl, fun y hy _ => ⟨(hb y hy).2.1, fun ξ => ?_⟩⟩
      have h1 := (hb y hy).2.2 ξ
      have h2 : 1 ≤ Real.exp (O.met.r c σ y / 2) := Real.one_le_exp (by linarith [hr1 c σ y])
      have h3 := Real.sqrt_nonneg (P.om c σ ch y ξ.ofLp)
      rw [Real.rpow_zero, mul_one]
      calc _ ≤ C * √(P.om c σ ch y ξ.ofLp) := h1
        _ ≤ max C 0 * √(P.om c σ ch y ξ.ofLp) := mul_le_mul_of_nonneg_right (le_max_left _ _) h3
        _ ≤ max C 0 * Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left h3 h2) (le_max_right _ _)
    · obtain ⟨ch, U, C, μ, hUo, hy₀, hUs, hμ, hb⟩ := hB' c σ ρ y₀ h₀
      refine ⟨ch, U, max C 0, μ, hUo, hy₀, hUs, le_max_right _ _, hμ, fun y hy hoff => ⟨(hb y hy hoff).1, fun ξ => ?_⟩⟩
      have h1 := (hb y hy hoff).2 ξ
      have hp : 0 ≤ O.met.r c σ y ^ μ := Real.rpow_nonneg (by linarith [hr1 c σ y]) _
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
        (Real.exp_pos _).le) (Real.sqrt_nonneg _)

  have glob : ∀ c σ (ρ : DV.Rt D.what₂.Tau O.N), ∃ C μ : ℝ, 0 ≤ C ∧ 0 ≤ μ ∧
      ∀ (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim), ∀ y ∈ ch.e.source, y ∈ offBd O.Φ c σ →
        DifferentiableAt ℝ (lineFn O x c σ ρ ∘ ch.e.symm) (ch.e y) ∧
        ∀ ξ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim, |fderiv ℝ (lineFn O x c σ ρ ∘ ch.e.symm) (ch.e y) ξ| ≤
          C * O.met.r c σ y ^ μ * Real.exp (O.met.r c σ y / 2) * √(P.om c σ ch y ξ.ofLp) := by
    intro c σ ρ
    choose ch U C μ hUo hy₀ hUs hC hμ hb using loc c σ ρ
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover U fun y _ => (hUo y).mem_nhds (hy₀ y)
    refine ⟨∑ y ∈ t, C y, ∑ y ∈ t, μ y, Finset.sum_nonneg fun _ _ => hC _, Finset.sum_nonneg fun _ _ => hμ _,
      fun ch' y hy hoff => ?_⟩
    obtain ⟨y₀, hy₀t, hyU⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    obtain ⟨hd, hbd⟩ := hb y₀ y hyU hoff
    obtain ⟨hd', hb'⟩ := transfer (P.om_kaehler c σ) (lineFn O x c σ ρ) ch' (ch y₀) hy (hUs y₀ hyU) hd _ hbd
    refine ⟨hd', fun ξ => (hb' ξ).trans ?_⟩
    have hr := hr1 c σ y
    have hC1 : C y₀ ≤ ∑ y ∈ t, C y := Finset.single_le_sum (f := C) (fun _ _ => hC _) hy₀t
    have hμ1 : μ y₀ ≤ ∑ y ∈ t, μ y := Finset.single_le_sum (f := μ) (fun _ _ => hμ _) hy₀t
    have hp1 : O.met.r c σ y ^ μ y₀ ≤ O.met.r c σ y ^ (∑ y ∈ t, μ y) := Real.rpow_le_rpow_of_exponent_le hr hμ1
    have hp0 : 0 ≤ O.met.r c σ y ^ μ y₀ := Real.rpow_nonneg (by linarith) _
    have h4 := mul_le_mul hC1 hp1 hp0 (Finset.sum_nonneg fun _ _ => hC _)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le) (Real.sqrt_nonneg _)

  haveI : Fintype O.s.Comp := Fintype.ofFinite _
  choose Cg μg hCg hμg hg using glob
  have hS0 : 0 ≤ ∑ c, ∑ σ, ∑ ρ, Cg c σ ρ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => hCg _ _ _
  refine ⟨2 * ∑ c, ∑ σ, ∑ ρ, Cg c σ ρ, ∑ c, ∑ σ, ∑ ρ, μg c σ ρ, mul_nonneg zero_le_two hS0,
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hμg _ _ _,
    fun c σ τ i ch y hy hoff => ?_⟩
  have hd := fun ρ => (hg c σ ρ ch y hy hoff).1
  have hsum : HasFDerivAt (fun v => 2 * ∑ ρ : DV.Rt D.what₂.Tau O.N, fund τ i ρ.1 ρ.2 * (lineFn O x c σ ρ ∘ ch.e.symm) v)
      ((2 : ℝ) • ∑ ρ : DV.Rt D.what₂.Tau O.N, fund τ i ρ.1 ρ.2 • fderiv ℝ (lineFn O x c σ ρ ∘ ch.e.symm) (ch.e y))
      (ch.e y) := by
    have := (HasFDerivAt.sum (u := Finset.univ) fun ρ _ => (hd ρ).hasFDerivAt.const_mul (fund τ i ρ.1 ρ.2)).const_mul 2
    simpa only [Finset.sum_apply] using this
  have e : psi O x c σ τ i ∘ ch.e.symm =
      fun v => 2 * ∑ ρ : DV.Rt D.what₂.Tau O.N, fund τ i ρ.1 ρ.2 * (lineFn O x c σ ρ ∘ ch.e.symm) v := rfl
  rw [e]
  refine ⟨hsum.differentiableAt, fun ξ => ?_⟩
  rw [hsum.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply, smul_eq_mul]
  set r := O.met.r c σ y
  set E := Real.exp (r / 2) * √(P.om c σ ch y ξ.ofLp)
  have hE0 : 0 ≤ E := hE _ _ _ _
  have hr := hr1 c σ y
  have hμall : ∀ ρ, μg c σ ρ ≤ ∑ c, ∑ σ, ∑ ρ, μg c σ ρ := fun ρ =>
    (Finset.single_le_sum (f := μg c σ) (fun _ _ => hμg _ _ _) (Finset.mem_univ ρ)).trans
      ((Finset.single_le_sum (f := fun σ => ∑ ρ, μg c σ ρ)
        (fun _ _ => Finset.sum_nonneg fun _ _ => hμg _ _ _) (Finset.mem_univ σ)).trans
      (Finset.single_le_sum (f := fun c => ∑ σ, ∑ ρ, μg c σ ρ)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hμg _ _ _) (Finset.mem_univ c)))
  have hCall : ∑ ρ, Cg c σ ρ ≤ ∑ c, ∑ σ, ∑ ρ, Cg c σ ρ :=
    (Finset.single_le_sum (f := fun σ => ∑ ρ, Cg c σ ρ)
        (fun _ _ => Finset.sum_nonneg fun _ _ => hCg _ _ _) (Finset.mem_univ σ)).trans
      (Finset.single_le_sum (f := fun c => ∑ σ, ∑ ρ, Cg c σ ρ)
        (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hCg _ _ _) (Finset.mem_univ c))
  have hterm : ∀ ρ : DV.Rt D.what₂.Tau O.N,
      |fund τ i ρ.1 ρ.2 * fderiv ℝ (lineFn O x c σ ρ ∘ ch.e.symm) (ch.e y) ξ| ≤
        Cg c σ ρ * (r ^ (∑ c, ∑ σ, ∑ ρ, μg c σ ρ) * E) := fun ρ => by
    have hf : |fund τ i ρ.1 ρ.2| ≤ 1 := by unfold fund; split_ifs <;> simp
    have hb := (hg c σ ρ ch y hy hoff).2 ξ
    have hp1 : r ^ μg c σ ρ ≤ r ^ (∑ c, ∑ σ, ∑ ρ, μg c σ ρ) := Real.rpow_le_rpow_of_exponent_le hr (hμall ρ)
    have hp0 : 0 ≤ r ^ μg c σ ρ := Real.rpow_nonneg (by linarith) _
    rw [abs_mul]
    calc |fund τ i ρ.1 ρ.2| * |fderiv ℝ (lineFn O x c σ ρ ∘ ch.e.symm) (ch.e y) ξ|
        ≤ 1 * (Cg c σ ρ * r ^ μg c σ ρ * E) := by
          rw [← mul_assoc (Cg c σ ρ * _)] at *
          exact mul_le_mul hf (by simpa only [E, mul_assoc] using hb) (abs_nonneg _) zero_le_one
      _ ≤ Cg c σ ρ * (r ^ (∑ c, ∑ σ, ∑ ρ, μg c σ ρ) * E) := by
          rw [one_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp1 hE0) (hCg _ _ _)
  rw [abs_mul, abs_two]
  calc 2 * |∑ ρ, fund τ i ρ.1 ρ.2 * fderiv ℝ (lineFn O x c σ ρ ∘ ch.e.symm) (ch.e y) ξ|
      ≤ 2 * ∑ ρ, Cg c σ ρ * (r ^ (∑ c, ∑ σ, ∑ ρ, μg c σ ρ) * E) :=
        mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ρ _ => hterm ρ))
          zero_le_two
    _ = 2 * (∑ ρ, Cg c σ ρ) * (r ^ (∑ c, ∑ σ, ∑ ρ, μg c σ ρ) * E) := by rw [← Finset.sum_mul, mul_assoc]
    _ ≤ 2 * (∑ c, ∑ σ, ∑ ρ, Cg c σ ρ) * (r ^ (∑ c, ∑ σ, ∑ ρ, μg c σ ρ) * E) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCall zero_le_two)
          (mul_nonneg (Real.rpow_nonneg (by linarith) _) hE0)
    _ = _ := by simp only [E]; ring

theorem gradSt : Hypotheses2 → HypothesesH → GradSt := gradSt_of_local GlobalTheory.T.log_metric_ratio_differentiable_chart GlobalTheory.T.log_metric_ratio_differentiable_nonneg

end GlobalTheory.GradFlag
