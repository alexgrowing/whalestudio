import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SemipositiveLeviOfLogMetricStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformLeviPositivityOnChartsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.VerticalFactorSmoothHermitianMetricStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedWeightDominatesEventuallyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedLeviLowerBoundEventuallyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AmpleOnGenericFibreOfSemipositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NefOnFibresAddNonnegStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

namespace MuPos

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} =
      ⋂ k, ⋃ i, {z : (Σ k, J k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem contDiffAt_logH {A : HermLine J} (hA : IsSmoothHerm A) {n : ℕ}
    {g : (Fin n → ℂ) → (Σ k, J k) → ℂ} {t : Fin n → ℂ} (hg : AnalyticAt ℂ g t)
    (hz : ∀ k, ∃ i, g t ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun s => Real.log (A.h (g s))) t := by
  have h1 : ContDiffAt ℝ 2 A.h (g t) :=
    ((hA.contDiffAt (isOpen_blockNonzero.mem_nhds hz)).of_le (by norm_cast))
  have h2 : ContDiffAt ℝ 2 g t := hg.restrictScalars.contDiffAt
  exact (h1.comp t h2).log (A.pos _ hz).ne'

theorem levi_const_mul {n : ℕ} {f : (Fin n → ℂ) → ℝ} {t : Fin n → ℂ} (c : ℝ) (hf : ContDiffAt ℝ 2 f t)
    (v : Fin n → ℂ) : levi (fun y => c * f y) t v = c * levi f t v := by
  have h := ReciprocityTheory.AnForm.levi_add_smul c (contDiffAt_const (c := (0 : ℝ))) hf v
  simp only [zero_add] at h
  rw [h]
  simp [levi]

theorem exists_analytic_sum {n : ℕ} (s : Finset ℕ) (f : ℕ → (Fin n → ℂ) → ℝ) (t : Fin n → ℂ)
    (h : ∀ r ∈ s, ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ u in 𝓝 t, f r u = (G u).re) :
    ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G t ∧ ∀ᶠ u in 𝓝 t, ∑ r ∈ s, f r u = (G u).re := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, analyticAt_const, by simp⟩
  | insert r s hr ih =>
    obtain ⟨G₁, hG₁, e₁⟩ := h r (Finset.mem_insert_self r s)
    obtain ⟨G₂, hG₂, e₂⟩ := ih fun r' hr' => h r' (Finset.mem_insert_of_mem hr')
    refine ⟨fun u => G₁ u + G₂ u, hG₁.add hG₂, ?_⟩
    filter_upwards [e₁, e₂] with u h₁ h₂
    rw [Finset.sum_insert hr, h₁, h₂, Complex.add_re]

theorem levi_split {n : ℕ} {fM fA F : (Fin n → ℂ) → ℝ} {G : (Fin n → ℂ) → ℂ} {t : Fin n → ℂ} {p q : ℝ}
    (hq : q ≠ 0) (hM : ContDiffAt ℝ 2 fM t) (hA : ContDiffAt ℝ 2 fA t) (hG : AnalyticAt ℂ G t)
    (hE : ∀ᶠ s in 𝓝 t, fM s = q * (F s + (G s).re) + p * fA s) (v : Fin n → ℂ) :
    levi fM t v = q * levi F t v + p * levi fA t v := by
  have hRe : ContDiffAt ℝ 2 (fun y => (G y).re) t :=
    Complex.reCLM.contDiff.contDiffAt.comp t (hG.restrictScalars.contDiffAt)
  have hMA : ContDiffAt ℝ 2 (fun y => fM y + (-p) * fA y) t := hM.add (contDiffAt_const.mul hA)
  have hR : ContDiffAt ℝ 2 (fun y => (fM y + (-p) * fA y) + (-q) * (G y).re) t :=
    hMA.add (contDiffAt_const.mul hRe)
  have hF : F =ᶠ[𝓝 t] fun y => q⁻¹ * ((fM y + (-p) * fA y) + (-q) * (G y).re) := by
    filter_upwards [hE] with y hy
    rw [hy]
    field_simp
    ring
  rw [ReciprocityTheory.AnForm.levi_congr hF v, levi_const_mul _ hR, ReciprocityTheory.AnForm.levi_add_smul (-q) hMA hRe,
    ReciprocityTheory.AnForm.levi_add_smul (-p) hM hA, ReciprocityTheory.AnForm.levi_re_analytic hG]
  field_simp
  ring

def sqDiv (A B : HermLine J) (p : ℕ) : HermLine J where
  a := (2 : ℤ) • A.a - (p : ℤ) • B.a
  h z := A.h z ^ 2 * (B.h z ^ p)⁻¹
  pos z hz := by
    have h1 := A.pos z hz
    have h2 := B.pos z hz
    positivity
  smul c z hc := by
    rw [A.smul c z hc, B.smul c z hc]
    have : ∀ k, ‖c k‖ ^ ((2 : ℤ) • A.a - (p : ℤ) • B.a) k =
        (‖c k‖ ^ A.a k) ^ 2 * ((‖c k‖ ^ B.a k) ^ p)⁻¹ := fun k => by
      have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [zpow_sub₀ h0, mul_comm (2 : ℤ), mul_comm (p : ℤ), _root_.zpow_mul, _root_.zpow_mul, div_eq_mul_inv]
      simp only [zpow_natCast, zpow_ofNat]
    simp only [this, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib, mul_pow, mul_inv]
    ring

theorem sqDiv_smooth {A B : HermLine J} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) (p : ℕ) :
    IsSmoothHerm (sqDiv A B p) :=
  (hA.pow 2).mul ((hB.pow p).inv fun z hz => (pow_pos (B.pos z hz) p).ne')

end MuPos

open MuPos

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

theorem chart_levi_split (D : ComponentData II Ψ K J Ω W) (S : Finset ℕ) (hS : S ⊆ D.S)
    (A : HermLine J) (hA : IsSmoothHerm A) (F : (Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) → ℝ) (a : Fin D.nCharts) (p q : ℕ) (hq : q ≠ 0)
    (t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) (ht : ‖t‖ ≤ 1 / 2)
    (hform : ∀ s ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1, Real.log (A.h ((D.chart a).γ s)) =
      q * (F s + ∑ r ∈ S, Real.log (D.vertFactor r ((D.chart a).γ s))) + p * Real.log (D.A'.h ((D.chart a).γ s)))
    (v : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) :
    levi (fun s => Real.log (A.h ((D.chart a).γ s))) t v =
      q * levi F t v + p * levi (fun s => Real.log (D.A'.h ((D.chart a).γ s))) t v := by
  have hb : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 := by
    rw [mem_ball_zero_iff]; linarith
  have hγ : AnalyticAt ℂ (D.chart a).γ t := (D.chart a).analytic t hb
  have hz : ∀ k, ∃ i, (D.chart a).γ t ⟨k, i⟩ ≠ 0 := ((D.chart a).mem t hb).1
  obtain ⟨G, hG, hGe⟩ := exists_analytic_sum S (fun r s => Real.log (D.vertFactor r ((D.chart a).γ s))) t
    fun r hr => (GlobalTheory.T.vertical_factor_smooth_hermitian_metric K J II Ψ Ω W D r (hS hr)).2 a t hb
  refine levi_split (G := G) (by exact_mod_cast hq) (contDiffAt_logH hA hγ hz)
    (contDiffAt_logH D.A'_pos.1 hγ hz) hG ?_ v
  filter_upwards [hGe, Metric.isOpen_ball.mem_nhds hb] with s h₁ h₂
  rw [hform s h₂, h₁]

theorem chart_levi_sqDiv (D : ComponentData II Ψ K J Ω W) (A : HermLine J) (hA : IsSmoothHerm A)
    (a : Fin D.nCharts) (p : ℕ) (t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) (ht : ‖t‖ ≤ 1 / 2) (v : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) :
    levi (fun s => Real.log ((sqDiv A D.A' p).h ((D.chart a).γ s))) t v =
      2 * levi (fun s => Real.log (A.h ((D.chart a).γ s))) t v -
        p * levi (fun s => Real.log (D.A'.h ((D.chart a).γ s))) t v := by
  have hb : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 := by
    rw [mem_ball_zero_iff]; linarith
  have hγ : AnalyticAt ℂ (D.chart a).γ t := (D.chart a).analytic t hb
  have hz : ∀ k, ∃ i, (D.chart a).γ t ⟨k, i⟩ ≠ 0 := ((D.chart a).mem t hb).1
  have h1 := contDiffAt_logH hA hγ hz
  have h2 := contDiffAt_logH D.A'_pos.1 hγ hz
  have hE : (fun s => Real.log ((sqDiv A D.A' p).h ((D.chart a).γ s))) =ᶠ[𝓝 t]
      fun s => 2 * Real.log (A.h ((D.chart a).γ s)) + (-(p : ℝ)) * Real.log (D.A'.h ((D.chart a).γ s)) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hb] with s hs
    have hzs : ∀ k, ∃ i, (D.chart a).γ s ⟨k, i⟩ ≠ 0 := ((D.chart a).mem s hs).1
    have p1 := A.pos _ hzs
    have p2 := D.A'.pos _ hzs
    show Real.log (A.h _ ^ 2 * (D.A'.h _ ^ p)⁻¹) = _
    rw [Real.log_mul (by positivity) (by positivity), Real.log_inv, Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [ReciprocityTheory.AnForm.levi_congr hE v, ReciprocityTheory.AnForm.levi_add_smul _ (contDiffAt_const.mul h1) h2,
    levi_const_mul _ h1]
  ring

theorem posU_of_nefOnFibres : PB.Inputs → ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), IsFullIntersectionSystem II → S'.IsTied → (∀ B : ℕ, 4 * D.f + 2 ≤ B → NefOnFibres (mCoordIdeal D.y) (muTwDeg Hd B)) → PosU S' := by
  intro hPB K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M w S' hII hT hNef B p q hB hp hpq
  obtain ⟨δ₀, hδ₀, hApos⟩ := GlobalTheory.T.uniform_levi_positivity_on_charts K J II Ψ Ω W D
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hq1 : 1 ≤ q := hp.trans hpq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hδ : 0 < p * δ₀ / (2 * q) := by positivity
  have hev := (GlobalTheory.T.regularized_weight_dominates_eventually K J II Ψ Ω W D Hd M w S' hT).and
    (GlobalTheory.T.regularized_levi_lower_bound_eventually K J II Ψ Ω W D Hd M w S' hT _ hδ)
  have key : ∀ LF LA V : ℝ, 0 ≤ V → -(p * δ₀ / (2 * q) * V) ≤ LF → δ₀ * V ≤ LA →
      0 ≤ q * LF + p * LA ∧ 0 ≤ 2 * (q * LF + p * LA) - p * LA := by
    intro LF LA V hV h1 h2
    have e1 : -(p * δ₀ / 2 * V) ≤ q * LF := by
      have := mul_le_mul_of_nonneg_left h1 hq0.le
      have e : (q : ℝ) * -(p * δ₀ / (2 * q) * V) = -(p * δ₀ / 2 * V) := by
        field_simp
      linarith
    have e2 : p * (δ₀ * V) ≤ p * LA := mul_le_mul_of_nonneg_left h2 hp0.le
    have e3 : 0 ≤ p * δ₀ * V := by positivity
    constructor <;> nlinarith
  obtain ⟨t₀, ht₀, hsub⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).1 hev
  refine ⟨t₀, ht₀, fun t' ht' ht'₀ => ?_⟩
  obtain ⟨⟨-, -, hMU⟩, hreg⟩ := hsub ⟨ht', ht'₀⟩
  obtain ⟨hsm, hdeg, hform⟩ := hMU B p q
  set A := MUc Hd S' B p q t' with hAdef
  have hsplit : ∀ (a : Fin D.nCharts) (t : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ), ‖t‖ ≤ 1 / 2 → ∀ v : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ,
      levi (fun s => Real.log (A.h ((D.chart a).γ s))) t v =
        q * levi (fun s => Real.log (S'.ref.h ((D.chart a).γ s)) + S'.bregWeight t' (M.proj ((D.chart a).γ s))) t v +
          p * levi (fun s => Real.log (D.A'.h ((D.chart a).γ s))) t v := by
    intro a t ht v
    refine chart_levi_split D (D.SB B) (Finset.filter_subset _ _) A hsm _ a p q (by omega) t ht (fun s hs => ?_) v
    exact hform _ ((D.chart a).mem s hs)
  have hsemi : IsSemipositiveH (mCoordIdeal D.y) A := by
    refine GlobalTheory.T.semipositive_levi_of_log_metric K J II Ψ Ω W D A hsm fun a t ht v => ?_
    have e := hsplit a t ht v
    have b1 := hreg a t ht v
    have b2 := hApos a t ht v
    rw [e]
    exact (key _ _ _ (by positivity) b1 b2).1
  have hN : IsSemipositiveH (mCoordIdeal D.y) (sqDiv A D.A' p) := by
    refine GlobalTheory.T.semipositive_levi_of_log_metric K J II Ψ Ω W D _ (sqDiv_smooth hsm D.A'_pos.1 p) fun a t ht v => ?_
    have e0 := chart_levi_sqDiv D A hsm a p t ht v
    have e := hsplit a t ht v
    have b1 := hreg a t ht v
    have b2 := hApos a t ht v
    rw [e0, e]
    exact (key _ _ _ (by positivity) b1 b2).2
  refine ⟨hsemi, ?_, ?_⟩
  · rw [hdeg]
    exact GlobalTheory.T.nef_on_fibres_add_nonneg hPB K J _ _ _ p q (hNef B hB) fun k => (D.a'_pos k).le
  · refine GlobalTheory.T.ample_on_generic_fibre_of_semipositive hPB II hII K J _ (sqDiv A D.A' p) A D.a' 2 p hN hsm D.a'_pos (by norm_num) hp ?_
    ext k
    simp [sqDiv, D.A'_deg]

end GlobalTheory.CompanionTheory.Ar.Cusp
