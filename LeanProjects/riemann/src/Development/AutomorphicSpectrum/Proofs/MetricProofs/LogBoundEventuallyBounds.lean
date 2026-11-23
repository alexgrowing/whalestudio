import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodMatrixLocalTrivialization
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SubframeDetLogGrowth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodsSubframeDetBounds
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPuncturedExpOrder
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PLogCoverDescent
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PAnalyticDerivBound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PGramEntryDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryBound

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section LogBoundAux

open scoped MatrixOrder

theorem logBound_radius_eq {n a : ℕ} (h : a ≤ n) (z : Fin n → ℂ) :
    chartRadius h z = Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖z i‖ ^ 2) else 0 := by
  rw [chartRadius, ← Finset.sum_filter]
  congr 1
  refine Finset.sum_bij (fun j _ => Fin.castLE h j) ?_ ?_ ?_ ?_
  · intro j _
    simp
  · intro j _ j' _ e
    exact Fin.castLE_injective h e
  · intro i hi
    have hi' : i.val < a := by simpa using hi
    exact ⟨⟨i.val, hi'⟩, Finset.mem_univ _, by ext; simp⟩
  · intro j _
    simp [cuspCoord]

theorem logBound_smul_one_le {k : ℕ} {s t : ℝ} (h : s ≤ t) :
    s • (1 : Matrix (Fin k) (Fin k) ℂ) ≤ t • (1 : Matrix (Fin k) (Fin k) ℂ) := by
  rw [Matrix.le_iff, ← sub_smul]
  exact Matrix.PosSemidef.one.smul (sub_nonneg.2 h)

theorem logBound_eventually_bounds {X : Type*} [TopologicalSpace X] {k : ℕ}
    (T : X → Matrix (Fin k) (Fin k) ℂ) (x : X) (hT : ContinuousAt T x) (hx : (T x).PosDef)
    (hp : ∀ᶠ y in 𝓝 x, (T y).PosSemidef) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧ ∀ᶠ y in 𝓝 x, δ • (1 : Matrix (Fin k) (Fin k) ℂ) ≤ T y ∧
      T y ≤ K • (1 : Matrix (Fin k) (Fin k) ℂ) := by
  have hdet0 : (T x).det ≠ 0 := hx.det_pos.ne'
  have hinv := GlobalTheory.CompanionTheory.Ar.Flat.continuousAt_matrix_inv T x hT hdet0
  have hdet : ContinuousAt (fun y => (T y).det) x :=
    (continuous_id.matrix_det).continuousAt.comp hT
  have htr : Continuous (fun M : Matrix (Fin k) (Fin k) ℂ => (M.trace).re) :=
    Complex.continuous_re.comp continuous_id.matrix_trace
  have h1 : ContinuousAt (fun y => ((T y).trace).re) x := htr.continuousAt.comp hT
  have h2 : ContinuousAt (fun y => (((T y)⁻¹).trace).re) x := htr.continuousAt.comp hinv
  obtain ⟨K, hK⟩ : ∃ K, K = max 1 (((T x).trace).re + 1) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = max 1 ((((T x)⁻¹).trace).re + 1) := ⟨_, rfl⟩
  have hK0 : 0 < K := hK ▸ lt_max_of_lt_left one_pos
  have hB0 : 0 < B := hB ▸ lt_max_of_lt_left one_pos
  have e1 : ∀ᶠ y in 𝓝 x, ((T y).trace).re < K :=
    h1.eventually_lt continuousAt_const (hK ▸ lt_max_of_lt_right (lt_add_one _))
  have e2 : ∀ᶠ y in 𝓝 x, (((T y)⁻¹).trace).re < B :=
    h2.eventually_lt continuousAt_const (hB ▸ lt_max_of_lt_right (lt_add_one _))
  refine ⟨B⁻¹, K, inv_pos.2 hB0, hK0, ?_⟩
  filter_upwards [hp, hdet.eventually_ne hdet0, e1, e2] with y hy hd y1 y2
  have hu : IsUnit (T y) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)
  have hPD : (T y).PosDef := hy.posDef_iff_isUnit.2 hu
  have hl : T y ≤ ((T y).trace).re • (1 : Matrix (Fin k) (Fin k) ℂ) :=
    GlobalTheory.le_re_trace_smul_one_of_posSemidef hy
  have hl2 : (T y)⁻¹ ≤ (((T y)⁻¹).trace).re • (1 : Matrix (Fin k) (Fin k) ℂ) :=
    GlobalTheory.le_re_trace_smul_one_of_posSemidef hPD.inv.posSemidef
  refine ⟨?_, hl.trans (logBound_smul_one_le y1.le)⟩
  have hh := GlobalTheory.inv_smul_one_le_inv_of_le_smul_one hPD.inv hB0
    (hl2.trans (logBound_smul_one_le y2.le))
  rwa [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu)] at hh

theorem logBound_inv_bounds {g m : ℕ} (Y : Matrix (Fin g) (Fin g) ℝ) (F : Matrix (Fin g) (Fin m) ℂ)
    {c D δ K : ℝ} (hc : 0 < c) (hD : 0 < D) (hδ : 0 < δ) (hK : 0 < K)
    (h1 : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef)
    (h2 : (D • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef)
    (h3 : δ • (1 : Matrix (Fin m) (Fin m) ℂ) ≤ Fᴴ * F)
    (h4 : Fᴴ * F ≤ K • (1 : Matrix (Fin m) (Fin m) ℂ)) :
    (Real.pi * (c⁻¹ * K))⁻¹ • (1 : Matrix (Fin m) (Fin m) ℂ) ≤
        (Real.pi • (Fᴴ * ((Y⁻¹).map Complex.ofReal)ᵀ * F))⁻¹ ∧
      (Real.pi • (Fᴴ * ((Y⁻¹).map Complex.ofReal)ᵀ * F))⁻¹ ≤
        (Real.pi * (D⁻¹ * δ))⁻¹ • (1 : Matrix (Fin m) (Fin m) ℂ) := by
  obtain ⟨b1, b2⟩ := GlobalTheory.CompanionTheory.Ar.Flat.subframe_inv_bounds Y hc hD h1 h2
  have t1 := GlobalTheory.transpose_le_transpose_of_le b1
  have t2 := GlobalTheory.transpose_le_transpose_of_le b2
  have e : ∀ t : ℝ, (t • (1 : Matrix (Fin g) (Fin g) ℂ))ᵀ = t • (1 : Matrix (Fin g) (Fin g) ℂ) := by
    intro t
    rw [Matrix.transpose_smul, Matrix.transpose_one]
  rw [e] at t1 t2
  have l1 := GlobalTheory.conjTranspose_mul_mul_le_of_le t1 F
  have l2 := GlobalTheory.conjTranspose_mul_mul_le_of_le t2 F
  have e2 : ∀ t : ℝ, Fᴴ * (t • (1 : Matrix (Fin g) (Fin g) ℂ)) * F = t • (Fᴴ * F) := by
    intro t
    simp [Matrix.mul_smul, Matrix.smul_mul]
  rw [e2] at l1 l2
  obtain ⟨S, hS⟩ : ∃ S, S = Fᴴ * ((Y⁻¹).map Complex.ofReal)ᵀ * F := ⟨_, rfl⟩
  rw [← hS] at l1 l2 ⊢
  have hpi := Real.pi_pos
  have p1 : (Real.pi * (D⁻¹ * δ)) • (1 : Matrix (Fin m) (Fin m) ℂ) ≤ Real.pi • S := by
    have q1 := GlobalTheory.real_smul_le_real_smul_of_le h3 (inv_pos.2 hD).le
    rw [smul_smul] at q1
    have q2 := GlobalTheory.real_smul_le_real_smul_of_le (q1.trans l1) hpi.le
    rwa [smul_smul] at q2
  have p2 : Real.pi • S ≤ (Real.pi * (c⁻¹ * K)) • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    have q1 := GlobalTheory.real_smul_le_real_smul_of_le h4 (inv_pos.2 hc).le
    rw [smul_smul] at q1
    have q2 := GlobalTheory.real_smul_le_real_smul_of_le (l2.trans q1) hpi.le
    rwa [smul_smul] at q2
  have ha : 0 < Real.pi * (D⁻¹ * δ) := by positivity
  have hb : 0 < Real.pi * (c⁻¹ * K) := by positivity
  have pa : ((Real.pi * (D⁻¹ * δ)) • (1 : Matrix (Fin m) (Fin m) ℂ)).PosDef :=
    Matrix.PosDef.one.smul ha
  have hΓ : (Real.pi • S).PosDef := GlobalTheory.posDef_of_le pa p1
  refine ⟨GlobalTheory.inv_smul_one_le_inv_of_le_smul_one hΓ hb p2, ?_⟩
  have i1 := GlobalTheory.inv_le_inv_of_posDef_of_le pa p1
  rwa [GlobalTheory.inv_real_smul_of_posDef Matrix.PosDef.one ha.ne', inv_one] at i1

theorem logBound_entry {g m : ℕ} (u : Fin m → Fin g → ℂ) (H A W : Matrix (Fin g) (Fin g) ℂ)
    (hA : A.det ≠ 0) (hW : A * H * Aᴴ = W) (p q : Fin m) :
    u q ⬝ᵥ H *ᵥ star (u p) =
      (((Matrix.of u * A⁻¹)ᵀ)ᴴ * Wᵀ * (Matrix.of u * A⁻¹)ᵀ) p q := by
  have hAu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have hinv1 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hAu
  have hinv2 : Aᴴ * (A⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hinv1, Matrix.conjTranspose_one]
  have hH : Matrix.of u * H * (Matrix.of u)ᴴ =
      (Matrix.of u * A⁻¹) * W * (Matrix.of u * A⁻¹)ᴴ := by
    rw [← hW, Matrix.conjTranspose_mul]
    have e : Matrix.of u * A⁻¹ * (A * H * Aᴴ) * ((A⁻¹)ᴴ * (Matrix.of u)ᴴ) =
        Matrix.of u * (A⁻¹ * A) * H * (Aᴴ * (A⁻¹)ᴴ) * (Matrix.of u)ᴴ := by
      simp only [Matrix.mul_assoc]
    rw [e, hinv1, hinv2]
    simp
  have e : ∀ G : Matrix (Fin m) (Fin g) ℂ, Gᵀᴴ * Wᵀ * Gᵀ = (G * W * Gᴴ)ᵀ := by
    intro G
    have : Gᵀᴴ = Gᴴᵀ := by
      ext i j
      simp
    rw [this, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [e, ← hH, Matrix.transpose_apply, Matrix.mul_assoc]
  rfl

theorem logBound_det_diffOn {n k : ℕ} {S : Set (Fin n → ℂ)} (B : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ)
    (hB : ∀ i j, DifferentiableOn ℂ (fun z => B z i j) S) :
    DifferentiableOn ℂ (fun z => (B z).det) S := by
  simp only [Matrix.det_apply']
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  have hp : ∀ s : Finset (Fin k), DifferentiableOn ℂ (fun z => ∏ i ∈ s, B z (σ i) i) S := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using differentiableOn_const _
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (hB _ _).mul ih
  exact (differentiableOn_const _).mul (hp _)

theorem logBound_inv_diffOn {n k : ℕ} {S : Set (Fin n → ℂ)} (A : (Fin n → ℂ) → Matrix (Fin k) (Fin k) ℂ)
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) S) (hd : ∀ z ∈ S, (A z).det ≠ 0) (i j : Fin k) :
    DifferentiableOn ℂ (fun z => (A z)⁻¹ i j) S := by
  have h1 := logBound_det_diffOn A hA
  have h2 : DifferentiableOn ℂ (fun z => (A z).adjugate i j) S := by
    simp only [Matrix.adjugate_apply]
    refine logBound_det_diffOn _ fun k l => ?_
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact differentiableOn_const _
    · exact hA _ _
  have e : (fun z => (A z)⁻¹ i j) = fun z => ((A z).det)⁻¹ * (A z).adjugate i j := by
    funext z
    simp [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  exact (h1.inv hd).mul h2

end LogBoundAux

open scoped MatrixOrder in

theorem logBound_subframe : ∀ (n a g m : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (u : Fin m → (Fin n → ℂ) → Fin g → ℂ) (Γ : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ), (∀ i, DifferentiableOn ℂ (u i) (Metric.ball 0 1)) → LinearIndependent ℂ (fun i => u i 0) → (∀ z i j, Γ z i j = Real.pi * (u j z ⬝ᵥ L.H z *ᵥ star (u i z))) → ∃ ρ c C : ℝ, 0 < ρ ∧ 0 < c ∧ 0 < C ∧ ∀ z ∈ Flat.punct n a ρ, ((Γ z)⁻¹ - (c : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ)).PosSemidef ∧ (((C * (Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖z i‖ ^ 2) else 0) : ℝ) : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) - (Γ z)⁻¹).PosSemidef ∧ ∀ p q, ‖fderiv ℝ (fun t => Γ t p q) z‖ ≤ C * Real.exp ((Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < a then Real.log (1 / ‖z i‖ ^ 2) else 0) / 2) := by
  intro n a g m Λ _ L u Γ hu hli hΓ
  obtain ⟨Q, A, hAd, hA0, hAH⟩ := GlobalTheory.CompanionTheory.Ar.Flat.exists_periodPolydisc_frame n a g Λ L
  obtain ⟨ρ₁, c, C₁, hρ₁, hρ₁1, hc, hb⟩ :=
    (ImTauBounds.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof LogCoverDescent.proof) n a g Q
  obtain ⟨ρh, hρh, hρh1, ⟨Ch, hCh⟩, -⟩ :=
    (HodgeDerivative.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof LogCoverDescent.proof) n a g Q
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hAc : ContinuousAt A 0 := by
    have : ContinuousOn A (Metric.ball 0 1) :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
    exact this.continuousAt (Metric.isOpen_ball.mem_nhds h0)
  have hdet : ContinuousAt (fun z => (A z).det) 0 :=
    (continuous_id.matrix_det).continuousAt.comp hAc
  obtain ⟨ρ₂, hρ₂, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((hdet.eventually_ne hA0).and (Metric.ball_mem_nhds (0 : Fin n → ℂ) one_pos))
  obtain ⟨S, hSdef⟩ : ∃ S, S = Metric.ball (0 : Fin n → ℂ) ρ₂ := ⟨_, rfl⟩
  have hSo : IsOpen S := hSdef ▸ Metric.isOpen_ball
  have hS0 : (0 : Fin n → ℂ) ∈ S := hSdef ▸ Metric.mem_ball_self hρ₂
  have hS1 : S ⊆ Metric.ball 0 1 := fun z hz => (hball z (hSdef ▸ hz)).2
  have hSd : ∀ z ∈ S, (A z).det ≠ 0 := fun z hz => (hball z (hSdef ▸ hz)).1
  let F : (Fin n → ℂ) → Matrix (Fin g) (Fin m) ℂ := fun y => (Matrix.of (fun i => u i y) * (A y)⁻¹)ᵀ
  have hinvd := logBound_inv_diffOn A (fun i j => (hAd i j).mono hS1) hSd
  have hFd : ∀ j l, DifferentiableOn ℂ (fun y => F y j l) S := by
    intro j l
    simp only [F, Matrix.transpose_apply, Matrix.mul_apply, Matrix.of_apply]
    refine DifferentiableOn.fun_sum fun k _ => ?_
    exact ((differentiableOn_pi.1 (hu l) k).mono hS1).mul (hinvd k j)
  have hFa : ∀ j l, AnalyticOnNhd ℂ (fun y => F y j l) S := fun j l =>
    GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hSo (hFd j l)
  have hKS : Metric.closedBall (0 : Fin n → ℂ) (ρ₂ / 2) ⊆ S :=
    hSdef ▸ Metric.closedBall_subset_ball (by linarith)
  choose Ab hAb0 hAb using fun j l => AnalyticDerivBound.proof (fun y => F y j l) S _ hSo (hFa j l)
    (isCompact_closedBall (0 : Fin n → ℂ) (ρ₂ / 2)) hKS
  obtain ⟨bF, hbF⟩ : ∃ bF, bF = ∑ j, ∑ l, Ab j l + 1 := ⟨_, rfl⟩
  have hbF0 : 0 < bF := by
    have : 0 ≤ ∑ j, ∑ l, Ab j l := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun l _ => (hAb0 j l).le
    linarith
  have hAbF : ∀ j l, Ab j l ≤ bF := fun j l => by
    have s1 := Finset.single_le_sum (f := fun l => Ab j l) (fun l _ => (hAb0 j l).le) (Finset.mem_univ l)
    have s2 := Finset.single_le_sum (f := fun j => ∑ l, Ab j l)
      (fun j _ => Finset.sum_nonneg fun l _ => (hAb0 j l).le) (Finset.mem_univ j)
    linarith

  have hFc : ContinuousAt F 0 := by
    have : ContinuousOn F S :=
      continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hFd i j).continuousOn
    exact this.continuousAt (hSo.mem_nhds hS0)
  have hc2 : Continuous (fun M : Matrix (Fin g) (Fin m) ℂ => Mᴴ * M) :=
    continuous_id.matrix_conjTranspose.matrix_mul continuous_id
  have hTc : ContinuousAt (fun y => (F y)ᴴ * F y) 0 := hc2.continuousAt.comp hFc
  have hinj : Function.Injective (F 0).mulVec := by
    have h1 : Function.Injective fun v : Fin m → ℂ => v ᵥ* Matrix.of (fun i => u i 0) :=
      Matrix.vecMul_injective_iff.2 hli
    have hu0 : IsUnit (A 0)⁻¹ :=
      (Matrix.isUnit_nonsing_inv_iff).2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hA0))
    have h2 := Matrix.vecMul_injective_of_isUnit hu0
    intro x y hxy
    simp only [F, Matrix.mulVec_transpose, ← Matrix.vecMul_vecMul] at hxy
    exact h1 (h2 hxy)
  obtain ⟨δ, K, hδ, hK, hev⟩ := logBound_eventually_bounds (fun y => (F y)ᴴ * F y) 0 hTc
    (Matrix.PosDef.conjTranspose_mul_self (F 0) hinj)
    (Eventually.of_forall fun y => Matrix.posSemidef_conjTranspose_mul_self _)
  obtain ⟨ρ₃, hρ₃, hb3⟩ := Metric.eventually_nhds_iff_ball.1 hev

  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = min (min ρ₁ ρh) (min (ρ₂ / 2) ρ₃) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := hρdef ▸ lt_min (lt_min hρ₁ hρh) (lt_min (by linarith) hρ₃)
  have hρρ₁ : ρ ≤ ρ₁ := hρdef ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hρρh : ρ ≤ ρh := hρdef ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hρρ₂ : ρ ≤ ρ₂ / 2 := hρdef ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hρρ₃ : ρ ≤ ρ₃ := hρdef ▸ (min_le_right _ _).trans (min_le_right _ _)
  have hpi := Real.pi_pos
  obtain ⟨C₂, hC₂⟩ : ∃ C₂, C₂ = max C₁ 1 := ⟨_, rfl⟩
  have hC₂0 : 0 < C₂ := hC₂ ▸ lt_max_of_lt_right one_pos
  obtain ⟨Ca, hCa⟩ : ∃ Ca, Ca = C₂ / (Real.pi * δ) := ⟨_, rfl⟩
  obtain ⟨Cb, hCb⟩ : ∃ Cb, Cb = Real.pi * ((g : ℝ) ^ 2 * (2 * bF ^ 2 * c⁻¹ + bF ^ 2 * |Ch|)) := ⟨_, rfl⟩
  have hCa0 : 0 < Ca := hCa ▸ by positivity
  have hCb0 : 0 ≤ Cb := hCb ▸ by positivity
  refine ⟨ρ, (Real.pi * (c⁻¹ * K))⁻¹, Ca + Cb + 1, hρ0, by positivity, by positivity, fun z hz => ?_⟩
  obtain ⟨hzb, hz0⟩ := hz
  have hzn : ‖z‖ < ρ := by simpa [dist_zero_right] using hzb
  have hzS : z ∈ S := hSdef ▸ (mem_ball_zero_iff.2 (by linarith))
  have hz1 : z ∈ Metric.ball (0 : Fin n → ℂ) 1 := hS1 hzS
  have hcusp : ∀ j : Fin a, cuspCoord L.a_le z j ≠ 0 := fun j => hz0 _ (by simp)
  have hzp : z ∈ puncturedChart L.a_le (Metric.ball (0 : Fin n → ℂ) 1) := ⟨hz1, hcusp⟩
  have hw := HodgeDerivative.logLift_mem L.a_le hzp
  have hexp := HodgeDerivative.expCover_logLift L.a_le hcusp
  have hid : ∀ y, y ∈ puncturedChart L.a_le (Metric.ball (0 : Fin n → ℂ) 1) → y ∈ S →
      Γ y = Real.pi • ((F y)ᴴ * ((Q.hodge y).map Complex.ofReal)ᵀ * F y) := by
    intro y hy hyS
    have hwy := HodgeDerivative.logLift_mem L.a_le hy
    have hey := HodgeDerivative.expCover_logLift L.a_le hy.2
    have hAy := hAH _ hwy
    rw [hey] at hAy
    ext p q
    rw [hΓ, Matrix.smul_apply, Complex.real_smul]
    congr 1
    exact logBound_entry (fun i => u i y) (L.H y) (A y) _ (hSd y hyS) hAy p q
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (Q.τ (logLift a z)).map Complex.im := ⟨_, rfl⟩
  obtain ⟨hlow, hup⟩ := hb _ hw (by
    rw [hexp]
    exact Metric.mem_closedBall.2 (by simpa [dist_zero_right] using hzn.le.trans hρρ₁))
  rw [hexp, ← hY] at hup
  rw [← hY] at hlow
  have hr1 := HodgeDerivative.one_le_chartRadius L.a_le hzp
  obtain ⟨r, hr⟩ : ∃ r, r = chartRadius L.a_le z := ⟨_, rfl⟩
  rw [← hr] at hup hr1
  have hr0 : 0 < r := by linarith
  have hup' : ((C₂ * r) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef := by
    have e : (C₂ * r) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y =
        ((C₁ * r) • (1 : Matrix (Fin g) (Fin g) ℝ) - Y) +
          ((C₂ - C₁) * r) • (1 : Matrix (Fin g) (Fin g) ℝ) := by
      rw [sub_mul, sub_smul]
      abel
    rw [e]
    exact hup.add (Matrix.PosSemidef.one.smul
      (mul_nonneg (sub_nonneg.mpr (hC₂ ▸ le_max_left _ _)) hr0.le))
  obtain ⟨hδz, hKz⟩ := hb3 z (mem_ball_zero_iff.2 (by linarith))
  obtain ⟨i1, i2⟩ := logBound_inv_bounds Y (F z) hc (mul_pos hC₂0 hr0) hδ hK hlow hup' hδz hKz
  have hΓz : Γ z = Real.pi • ((F z)ᴴ * ((Y⁻¹).map Complex.ofReal)ᵀ * F z) := by
    rw [hY]
    exact hid z hzp hzS
  rw [← hΓz] at i1 i2
  have hcast : ∀ t : ℝ, (t : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) =
      t • (1 : Matrix (Fin m) (Fin m) ℂ) := by
    intro t
    ext i j
    simp [Matrix.smul_apply]
  rw [← logBound_radius_eq L.a_le z, ← hr]
  refine ⟨?_, ?_, fun p q => ?_⟩
  · rw [hcast]
    exact Matrix.le_iff.1 i1
  · rw [hcast]
    refine Matrix.le_iff.1 (i2.trans (logBound_smul_one_le ?_))
    have e : (Real.pi * ((C₂ * r)⁻¹ * δ))⁻¹ = Ca * r := by
      rw [hCa]
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (by linarith) hr0.le
  · obtain ⟨Z, hZ⟩ : ∃ Z : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℝ, Z = fun y => (Q.hodge y)ᵀ :=
      ⟨_, rfl⟩
    have hEq : (fun t => Γ t p q) =ᶠ[𝓝 z]
        fun t => Real.pi • ((F t)ᴴ * (Z t).map (fun x : ℝ => (x : ℂ)) * F t) p q := by
      have hU : puncturedChart L.a_le (Metric.ball (0 : Fin n → ℂ) 1) ∩ S ∈ 𝓝 z :=
        ((HodgeDerivative.isOpen_punctured L.a_le).inter hSo).mem_nhds ⟨hzp, hzS⟩
      filter_upwards [hU] with y hy
      rw [hid y hy.1 hy.2, Matrix.smul_apply, hZ]
      rfl
    have hE1 : 1 ≤ Real.exp (r / 2) := Real.one_le_exp (by positivity)
    have hzK : z ∈ Metric.closedBall (0 : Fin n → ℂ) (ρ₂ / 2) :=
      mem_closedBall_zero_iff.2 (by linarith)
    have hZf : ∀ j l, DifferentiableAt ℝ (fun y => Z y j l) z ∧ |Z z j l| ≤ c⁻¹ ∧
        ‖fderiv ℝ (fun y => Z y j l) z‖ ≤ |Ch| * Real.exp (r / 2) := by
      intro j l
      obtain ⟨d1, -, d3⟩ := hCh z (mem_closedBall_zero_iff.2 (by linarith)) hzp l j
      subst hZ
      refine ⟨d1, ?_, d3.trans ?_⟩
      · have := InvEntryBound.proof g Y c hc hlow l j
        rw [hY] at this
        exact this
      · rw [← hr]
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
    have hFf : ∀ j l, DifferentiableAt ℝ (fun y => F y j l) z ∧ ‖F z j l‖ ≤ bF ∧
        ‖fderiv ℝ (fun y => F y j l) z‖ ≤ bF := fun j l => by
      obtain ⟨d1, d2, d3⟩ := hAb j l z hzK
      exact ⟨d1, d2.trans (hAbF j l), d3.trans (hAbF j l)⟩
    obtain ⟨d1, -, d3⟩ := GramEntryDeriv.proof g m F Z z bF c⁻¹ (|Ch| * Real.exp (r / 2)) hFf hZf p q
    rw [hEq.fderiv_eq, fderiv_fun_const_smul d1, norm_smul, Real.norm_eq_abs, abs_of_pos hpi]
    have hci : 0 < c⁻¹ := inv_pos.2 hc
    have s1 : 2 * bF ^ 2 * c⁻¹ ≤ 2 * bF ^ 2 * c⁻¹ * Real.exp (r / 2) :=
      le_mul_of_one_le_right (by positivity) hE1
    calc Real.pi * ‖fderiv ℝ (fun q_1 => ((F q_1)ᴴ * (Z q_1).map (fun x : ℝ => (x : ℂ)) * F q_1) p q) z‖
        ≤ Real.pi * ((g : ℝ) ^ 2 * (2 * bF ^ 2 * c⁻¹ + bF ^ 2 * (|Ch| * Real.exp (r / 2)))) := by
          gcongr
      _ ≤ Real.pi * ((g : ℝ) ^ 2 * (2 * bF ^ 2 * c⁻¹ * Real.exp (r / 2) +
            bF ^ 2 * (|Ch| * Real.exp (r / 2)))) := by
          gcongr
      _ = Cb * Real.exp (r / 2) := by
          rw [hCb]
          ring
      _ ≤ (Ca + Cb + 1) * Real.exp (r / 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end GlobalTheory.CompanionTheory.Ar.Cusp
