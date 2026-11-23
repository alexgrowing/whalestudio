import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.PeriodIntegrals.QuotInv
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiffQuotientBesselMapTendstoStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement

noncomputable section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal NNReal

namespace GlobalTheory.BesselFixed

theorem integrable_and_integral_norm_le_of_lintegral_sq_le {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] (μ : Measure X) [IsFiniteMeasure μ]
    (C : ℝ≥0∞) (hC : C ≠ ⊤) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f : X → E) (t : ℝ≥0), AEStronglyMeasurable f μ →
      ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ ≤ C * (t : ℝ≥0∞) ^ 2 → Integrable f μ ∧ ∫ x, ‖f x‖ ∂μ ≤ K * t := by
  have hK : C ^ (1 / 2 : ℝ) * (μ Set.univ) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _))
  refine ⟨(C ^ (1 / 2 : ℝ) * (μ Set.univ) ^ (1 / 2 : ℝ)).toReal, ENNReal.toReal_nonneg, fun f t hf h => ?_⟩
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun x => ‖f x‖ₑ) (g := fun _ => 1) hf.enorm aemeasurable_const
  have h2 : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤ C ^ (1 / 2 : ℝ) * t := by
    have : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ≤ C * (t : ℝ≥0∞) ^ 2 := by
      refine le_trans (le_of_eq ?_) h
      refine lintegral_congr fun x => ?_
      rw [ENNReal.rpow_two]; rfl
    refine (ENNReal.rpow_le_rpow this (by norm_num)).trans (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_two, ← ENNReal.rpow_mul]
    norm_num
  have h3 : ∫⁻ x, ‖f x‖ₑ ∂μ ≤ C ^ (1 / 2 : ℝ) * (μ Set.univ) ^ (1 / 2 : ℝ) * t := by
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h1
    refine h1.trans ?_
    calc _ ≤ (C ^ (1 / 2 : ℝ) * t) * (μ Set.univ) ^ (1 / 2 : ℝ) := by gcongr
      _ = _ := by ring
  have h4 : C ^ (1 / 2 : ℝ) * (μ Set.univ) ^ (1 / 2 : ℝ) * t ≠ ⊤ := ENNReal.mul_ne_top hK ENNReal.coe_ne_top
  refine ⟨⟨hf, lt_of_le_of_lt h3 h4.lt_top⟩, ?_⟩
  rw [integral_norm_eq_lintegral_enorm hf]
  refine (ENNReal.toReal_mono h4 h3).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul]; simp

theorem ae_fixed {X Y H E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ν : Measure X) (μ : Measure Y) [SigmaFinite ν] [SigmaFinite μ] (D : Submodule ℂ H) (P : H → X → E)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hm : ∀ v ∈ D, AEStronglyMeasurable (P v) ν)
    (hb : ∀ v ∈ D, ∫⁻ x, (‖P v x‖₊ : ℝ≥0∞) ^ 2 ∂ν ≤ C * (‖v‖₊ : ℝ≥0∞) ^ 2)
    (hadd : ∀ v ∈ D, ∀ v' ∈ D, ∀ᵐ x ∂ν, P (v + v') x = P v x + P v' x)
    (hsm : ∀ c : ℂ, ∀ v ∈ D, ∀ᵐ x ∂ν, P (c • v) x = c • P v x)
    (τ : Y → H) (hτ : ∀ᵐ g ∂μ, τ g ∈ D ∧ ‖τ g‖ ≤ 1) (e : Y → ℂ) (he : Integrable e μ) (w : H) (hw : w ∈ D)
    (hS : ∀ u : H, ∫ g, e g * ⟪u, τ g⟫_ℂ ∂μ = ⟪u, w⟫_ℂ)
    (hj : AEStronglyMeasurable (fun p : X × Y => P (τ p.2) p.1) (ν.prod μ)) :
    ∀ᵐ x ∂ν, ∫ g, e g • P (τ g) x ∂μ = P w x := by
  have key : ∀ s : Set X, MeasurableSet s → ν s < ⊤ →
      IntegrableOn (fun x => ∫ g, e g • P (τ g) x ∂μ) s ν ∧ IntegrableOn (P w) s ν ∧
      ∫ x in s, (∫ g, e g • P (τ g) x ∂μ) ∂ν = ∫ x in s, P w x ∂ν := by
    intro s _ hs
    haveI : IsFiniteMeasure (ν.restrict s) := ⟨by simpa using hs⟩
    obtain ⟨K, hK0, hK⟩ := integrable_and_integral_norm_le_of_lintegral_sq_le (E := E) (ν.restrict s) C hC
    have hP : ∀ v ∈ D, Integrable (P v) (ν.restrict s) ∧ ∫ x, ‖P v x‖ ∂(ν.restrict s) ≤ K * ‖v‖ := fun v hv =>
      hK (P v) ‖v‖₊ (hm v hv).restrict ((lintegral_mono' Measure.restrict_le_self le_rfl).trans (hb v hv))
    have hj' : AEStronglyMeasurable (fun p : X × Y => e p.2 • P (τ p.2) p.1) ((ν.restrict s).prod μ) := by
      refine AEStronglyMeasurable.smul he.aestronglyMeasurable.comp_snd (hj.mono_ac ?_)
      exact Measure.AbsolutelyContinuous.prod Measure.absolutelyContinuous_restrict Measure.AbsolutelyContinuous.rfl
    have hI : Integrable (fun p : X × Y => e p.2 • P (τ p.2) p.1) ((ν.restrict s).prod μ) := by
      rw [integrable_prod_iff' hj']
      refine ⟨hτ.mono fun g hg => (hP _ hg.1).1.smul (e g), ?_⟩
      refine Integrable.mono' (he.norm.mul_const K) hj'.norm.prod_swap.integral_prod_right' (hτ.mono fun g hg => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
      simp only [norm_smul, integral_const_mul]
      refine mul_le_mul_of_nonneg_left ((hP _ hg.1).2.trans ?_) (norm_nonneg _)
      exact mul_le_of_le_one_right hK0 hg.2
    refine ⟨hI.integral_prod_left, (hP w hw).1, ?_⟩
    rw [integral_integral_swap (f := fun x g => e g • P (τ g) x) hI]
    refine ext_inner_left ℂ fun ξ => ?_
    let φ : D →ₗ[ℂ] ℂ :=
      { toFun := fun v => ⟪ξ, ∫ x in s, P v x ∂ν⟫_ℂ
        map_add' := fun v v' => by
          rw [← inner_add_right, ← integral_add (hP _ v.2).1 (hP _ v'.2).1]
          congr 1
          exact integral_congr_ae (ae_restrict_of_ae (hadd _ v.2 _ v'.2))
        map_smul' := fun c v => by
          rw [RingHom.id_apply, smul_eq_mul, ← inner_smul_right, ← integral_smul]
          congr 1
          exact integral_congr_ae (ae_restrict_of_ae (hsm c _ v.2)) }
    have hφ : ∀ v : D, ‖φ v‖ ≤ (‖ξ‖ * K) * ‖v‖ := fun v => by
      refine (norm_inner_le_norm _ _).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (hP _ v.2).2) (norm_nonneg _)
    obtain ⟨ψ, hψ, -⟩ := exists_extension_norm_eq D (φ.mkContinuous _ hφ)
    have hu : ∀ v ∈ D, ⟪(InnerProductSpace.toDual ℂ H).symm ψ, v⟫_ℂ = ⟪ξ, ∫ x in s, P v x ∂ν⟫_ℂ := fun v hv => by
      rw [InnerProductSpace.toDual_symm_apply]
      exact hψ ⟨v, hv⟩
    rw [← hu w hw, ← hS, ← integral_inner hI.integral_prod_right]
    refine integral_congr_ae (hτ.mono fun g hg => ?_)
    simp only
    rw [hu _ hg.1, integral_smul, inner_smul_right]
  exact ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s h h' => (key s h h').1) (fun s h h' => (key s h h').2.1)
    (fun s h h' => (key s h h').2.2)

variable {k r : ℕ}

theorem sm_indicator {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E] {S : Set (Mat k r)}
    (hS : IsClosed S) {f : Mat k r → E} (hf : ContinuousOn f S) :
    StronglyMeasurable (Set.indicator {x : Mt k r | Matrix.of x ∈ S} fun x => f (Matrix.of x)) := by
  classical
  borelize E
  have hm : MeasurableSet {x : Mt k r | Matrix.of x ∈ S} := IsClosed.measurableSet (α := Mt k r) hS
  have hf' : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) {x : Mt k r | Matrix.of x ∈ S} := hf
  have := hf'.measurable_piecewise (g := fun _ => (0 : E)) continuousOn_const hm
  rw [← Set.piecewise_eq_indicator]
  exact this.stronglyMeasurable

theorem aesm_of_continuousOn {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E] {S : Set (Mat k r)}
    (hS : IsClosed S) {f : Mat k r → E} (hf : ContinuousOn f S) {μ : Measure (Mt k r)}
    (hμ : ∀ᵐ x ∂μ, Matrix.of x ∈ S) : AEStronglyMeasurable (fun x : Mt k r => f (Matrix.of x)) μ :=
  (sm_indicator hS hf).aestronglyMeasurable.congr (hμ.mono fun x hx => Set.indicator_of_mem (by exact hx) _)

theorem continuous_mulM : Continuous fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 :=
  Continuous.matrix_mul (X := Mt k r × Mt k r) (A := fun p => (Matrix.of p.1 : Mat k r))
    (B := fun p => (Matrix.of p.2 : Mat k r)) continuous_fst continuous_snd

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem fdeg_eq {σ : Mat k r → (H →L[ℂ] H)} {w : H} {μG : Measure (Mt k r)} {d : ℝ} (h : SchurH μG σ d)
    (hw : ‖w‖ = 1) : fdegH μG σ w = d := by
  have h1 := (h.2 w w w w).2
  have h2 : ∀ g : Mt k r, coef σ w w (Matrix.of g) * star (coef σ w w (Matrix.of g)) =
      ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; rfl
  simp only [h2] at h1
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, hw] at h1
  have h3 : ∫ g : Mt k r, ‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 ∂μG = 1 / d := by
    apply Complex.ofReal_injective
    rw [h1]; simp
  unfold fdegH
  rw [h3, hw]; simp

theorem continuousOn_eFun {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (w : H) (μG : Measure (Mt k r)) :
    ContinuousOn (eFun μG σ w) (GG k r) :=
  continuousOn_const.mul (continuousOn_const.inner (hσ.2.2 w)).star

theorem integrable_eFun {σ : Mat k r → (H →L[ℂ] H)} {w : H} {a d : ℝ} {μG : Measure (Mt k r)}
    (h : Std σ w a μG d) (hG : IsClosedSub k r (GG k r)) :
    Integrable (fun g : Mt k r => eFun μG σ w (Matrix.of g)) μG := by
  obtain ⟨hk, hσ, -, hw, hμ, -, ha, hdec, -⟩ := h
  have hae : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r := hμ.2.2.1
  have hwD : w ∈ DD σ w := by
    have := mem_DD σ w hG.2.2.1
    rwa [hσ.1.1] at this
  obtain ⟨C, hC⟩ := hdec w hwD w hwD
  have hn : (2 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ 2 * r + k + 1)
  have hA : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < a := by
    refine lt_of_lt_of_le ?_ ha
    have := pow_lt_pow_right₀ (a := ((2 * r + k + 1 : ℕ) : ℝ)) (by linarith) (by norm_num : 2 < 5)
    linarith
  have hfin := GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r _ μG a hG hμ hA
  refine ⟨aesm_of_continuousOn hG.2.1 (continuousOn_eFun hσ w μG) hae, ?_⟩
  have hle : ∫⁻ g, ‖eFun μG σ w (Matrix.of g)‖ₑ ∂μG ≤
      ∫⁻ g, ENNReal.ofReal (|fdegH μG σ w| * |C|) * ENNReal.ofReal (opn (Matrix.of g) ^ (-a)) ∂μG := by
    refine lintegral_mono_ae (hae.mono fun g hg => ?_)
    rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm_eq_enorm]
    refine ENNReal.ofReal_le_ofReal ?_
    unfold eFun
    rw [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ((hC _ hg).trans ?_) (abs_nonneg _)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (opn_nonneg _) _)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hle
  exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)

theorem weak_fixed {σ : Mat k r → (H →L[ℂ] H)} {w : H} {μG : Measure (Mt k r)} {d : ℝ} (h : SchurH μG σ d)
    (hw : ‖w‖ = 1) (u : H) :
    ∫ g : Mt k r, eFun μG σ w (Matrix.of g) * ⟪u, σ (Matrix.of g) w⟫_ℂ ∂μG = ⟪u, w⟫_ℂ := by
  have h1 := (h.2 w u w w).2
  have h2 : ∀ g : Mt k r, eFun μG σ w (Matrix.of g) * ⟪u, σ (Matrix.of g) w⟫_ℂ =
      (d : ℂ) * (coef σ w u (Matrix.of g) * star (coef σ w w (Matrix.of g))) := fun g => by
    unfold eFun coef
    rw [fdeg_eq h hw]; ring
  simp only [h2]
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast h.1.ne'
  rw [integral_const_mul, h1, inner_self_eq_norm_sq_to_K, hw]
  field_simp
  simp

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]

theorem equiv_rconv {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat k r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)}
    (hπ : IsURepOn (UWset k r z) π) (hG : IsClosedSub k r (GG k r)) {μG : Measure (Mt k r)}
    (hae : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r) (e : Mat k r → ℂ) {Φ : Mat k r → Wp} (hΦ : IsSPsiEquiv z ψ π Φ) :
    IsSPsiEquiv z ψ π (rconv μG e Φ) := by
  intro h hh m hm g hg
  let L : Wp →ₗᵢ[ℂ] Wp := ⟨(π h : Wp →ₗ[ℂ] Wp), hπ.2.1 h hh⟩
  unfold rconv
  have := L.integral_comp_comm (μ := μG) fun y => e (Matrix.of y) • Φ (g * Matrix.of y)
  change _ = π h _ at this
  rw [← this, ← integral_smul]
  refine integral_congr_ae (hae.mono fun y hy => ?_)
  simp only
  rw [mul_assoc (h * m), hΦ h hh m hm _ (hG.2.2.2.1 _ hg _ hy), smul_comm, L.map_smul]
  rfl

theorem ae_of_quot {z : Fin (2 * r + k + 1) → ℂ} {ψ : Mat k r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)}
    {μG μS ν : Measure (Mt k r)} (hq : IsQuotMeas μG μS ν) (hS : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z)
    (hν : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r) (hμ : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r)
    (hG : IsClosedSub k r (GG k r)) {Φ Ψ : Mat k r → Wp} (hΦ : IsSPsiEquiv z ψ π Φ) (hΨ : IsSPsiEquiv z ψ π Ψ)
    {Φ' Ψ' : Mt k r → Wp} (mΦ : StronglyMeasurable Φ') (mΨ : StronglyMeasurable Ψ')
    (eΦ : ∀ x, Matrix.of x ∈ GG k r → Φ' x = Φ (Matrix.of x)) (eΨ : ∀ x, Matrix.of x ∈ GG k r → Ψ' x = Ψ (Matrix.of x))
    (h : ∀ᵐ x ∂ν, Φ (Matrix.of x) = Ψ (Matrix.of x)) : ∀ᵐ x ∂μG, Φ (Matrix.of x) = Ψ (Matrix.of x) := by
  have hA : MeasurableSet {x | Φ' x = Ψ' x}ᶜ := (mΦ.measurableSet_eq_fun mΨ).compl
  have h0 : μG {x | Φ' x = Ψ' x}ᶜ = 0 := by
    rw [← lintegral_indicator_one hA, hq _ (measurable_one.indicator hA)]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hν, h] with x hx hx'
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hS] with s hs
    obtain ⟨a, ha, m, hm, hs⟩ := hs
    have hmem : Matrix.of s * Matrix.of x ∈ GG k r := by
      rw [hs]; exact hG.2.2.2.1 _ (hG.2.2.2.1 _ ha.1 _ hm.1) _ hx
    refine Set.indicator_of_notMem ?_ _
    simp only [Set.mem_compl_iff, not_not, Set.mem_setOf_eq]
    rw [eΦ (fun i j => (Matrix.of s * Matrix.of x) i j) hmem, eΨ (fun i j => (Matrix.of s * Matrix.of x) i j) hmem]
    change Φ (Matrix.of s * Matrix.of x) = Ψ (Matrix.of s * Matrix.of x)
    rw [hs, hΦ a ha m hm _ hx, hΨ a ha m hm _ hx, hx']
  have h1 : ∀ᵐ x ∂μG, Φ' x = Ψ' x := h0
  filter_upwards [h1, hμ] with x hx hx'
  rw [← eΦ x hx', ← eΨ x hx', hx]

theorem nonVan_of_bessel : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a d : ℝ) (μG μS νS : Measure (Mt k r)) (z : (Fin (2 * r + k + 1) → ℂ)) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (B : H → Wp), StdSm σ w a μG d → Side z π μS → IsQuotMeas μG μS νS → IsBesselMapSm z (psiGen k r z c) σ π B → l2SG νS (fun g => B (σ g w)) ≠ 0 → l2SG νS (fun g => B (σ g w)) ≠ ⊤ → (∀ v ∈ smoothVecs σ, l2SG νS (fun g => B (σ g v)) = l2SG νS (fun g => B (σ g w)) * (‖v‖₊ : ℝ≥0∞) ^ 2) → NonVan z (psiGen k r z c) σ π w μG νS := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a d μG μS ν z c π B hstd hside hq hB h0 htop hnorm
  obtain ⟨hstd, hws⟩ := hstd
  obtain ⟨hz, hT, hπ, hμS, -⟩ := hside
  obtain ⟨hG, -, -, hS, -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  have he := integrable_eFun hstd hG
  obtain ⟨-, hσ, -, hw, hμ, hsch, -, -, -⟩ := hstd
  obtain ⟨hσf, hν, -⟩ := GlobalTheory.T.weil_formula_besselUnitary_integrable k r _ μG μS ν hS hμ hμS ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hμS) hq
  haveI := hμ.1
  haveI : SecondCountableTopology Wp := by
    haveI : ProperSpace Wp := FiniteDimensional.proper_rclike ℂ Wp
    infer_instance
  have hνG : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := hν
  have hμG : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r := hμ.2.2.1
  have hμSS : ∀ᵐ x ∂μS, Matrix.of x ∈ Sset k r z := hμS.2.2.1
  obtain ⟨-, -, hDV, htr, hV⟩ := GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hσ
  have hDs : ∀ v ∈ DD σ w, IsSmoothVec σ v := fun v hv => (hV hws).1 v (hDV hv)
  have hcont : ∀ v, IsSmoothVec σ v → ContinuousOn (fun g => B (σ g v)) (GG k r) := fun v hv =>
    (GlobalTheory.T.diffQuotient_besselMap_tendsto k r σ z _ π B v 0 hσ hB hv (by simp [InLieHpk])).2.1
  have hmul : ∀ x ∈ GG k r, ∀ g ∈ GG k r, σ (x * g) w = σ x (σ g w) := fun x hx g hg => by
    rw [hσ.1.2 x hx g hg]; rfl
  have hwD : w ∈ DD σ w := by
    have := mem_DD σ w hG.2.2.1
    rwa [hσ.1.1] at this
  set Φ : Mat k r → Wp := fun g => B (σ g w) with hΦ
  have hΦe : IsSPsiEquiv z (psiGen k r z c) π Φ := fun h hh m hm g hg => by
    simp only [hΦ]
    rw [hmul _ (hG.2.2.2.1 _ hh.1 _ hm.1) _ hg]
    exact hB.2.2.1 h hh m hm _ ((htr w hws).1 g hg)
  set e : Mat k r → ℂ := eFun μG σ w with hedef
  have hWe : IsSPsiEquiv z (psiGen k r z c) π (rconv μG e Φ) := equiv_rconv hπ hG hμG e hΦe
  have mΦ := sm_indicator hG.2.1 (hcont w hws)
  have me := sm_indicator hG.2.1 (continuousOn_eFun hσ w μG)
  set Φ' := Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => Φ (Matrix.of x) with hΦ'
  set e' := Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r} fun x => e (Matrix.of x) with he'
  have eΦ : ∀ x, Matrix.of x ∈ GG k r → Φ' x = Φ (Matrix.of x) := fun x hx => Set.indicator_of_mem (by exact hx) _
  have ee : ∀ x, Matrix.of x ∈ GG k r → e' x = e (Matrix.of x) := fun x hx => Set.indicator_of_mem (by exact hx) _
  have mΦ2 : StronglyMeasurable fun p : Mt k r × Mt k r => Φ' (lmulM (Matrix.of p.1) p.2) :=
    mΦ.comp_measurable continuous_mulM.measurable
  have mW : StronglyMeasurable fun x : Mt k r => ∫ g, e' g • Φ' (lmulM (Matrix.of x) g) ∂μG :=
    StronglyMeasurable.integral_prod_right' (f := fun p : Mt k r × Mt k r => e' p.2 • Φ' (lmulM (Matrix.of p.1) p.2))
      ((me.comp_measurable measurable_snd).smul mΦ2)
  have eW : ∀ x : Mt k r, Matrix.of x ∈ GG k r →
      ∫ g, e' g • Φ' (lmulM (Matrix.of x) g) ∂μG = rconv μG e Φ (Matrix.of x) := fun x hx => by
    refine integral_congr_ae (hμG.mono fun g hg => ?_)
    simp only
    rw [ee g hg, eΦ (lmulM (Matrix.of x) g) (hG.2.2.2.1 _ hx _ hg)]; rfl
  have hfix : ∀ᵐ x ∂ν, rconv μG e Φ (Matrix.of x) = Φ (Matrix.of x) := by
    have := ae_fixed ν μG (DD σ w) (fun v x => B (σ (Matrix.of x) v)) (l2SG ν Φ) htop
      (fun v hv => aesm_of_continuousOn hG.2.1 (hcont v (hDs v hv)) hνG)
      (fun v hv => (hnorm v (hDs v hv)).le)
      (fun v hv v' hv' => hνG.mono fun x hx => by
        simp only [map_add]
        exact hB.1 _ ((htr v (hDs v hv)).1 _ hx) _ ((htr v' (hDs v' hv')).1 _ hx))
      (fun t v hv => hνG.mono fun x hx => by
        simp only [map_smul]
        exact hB.2.1 t _ ((htr v (hDs v hv)).1 _ hx))
      (fun g => σ (Matrix.of g) w) (hμG.mono fun g hg => ⟨mem_DD σ w hg, by rw [hσ.2.1 _ hg, hw]⟩)
      (fun g => e (Matrix.of g)) he w hwD (weak_fixed hsch hw) (mΦ2.aestronglyMeasurable.congr (by
        filter_upwards [Measure.quasiMeasurePreserving_fst.ae hνG, Measure.quasiMeasurePreserving_snd.ae hμG]
          with p h1 h2
        rw [eΦ (lmulM (Matrix.of p.1) p.2) (hG.2.2.2.1 _ h1 _ h2), ← hmul _ h1 _ h2]; rfl))
    filter_upwards [this, hνG] with x hx hx'
    refine Eq.trans ?_ hx
    refine integral_congr_ae (hμG.mono fun g hg => ?_)
    simp only [hΦ]
    rw [hmul _ hx' _ hg]
  have hfixG : ∀ᵐ x ∂μG, rconv μG e Φ (Matrix.of x) = Φ (Matrix.of x) :=
    ae_of_quot hq hμSS hνG hμG hG hWe hΦe mW mΦ eW eΦ hfix
  have hl2 : l2SG ν (rconv μG e Φ) = l2SG ν Φ := lintegral_congr_ae (hfix.mono fun x hx => by simp only [hx])
  refine ⟨rconv μG e Φ, mW.aestronglyMeasurable.congr (hμG.mono eW), mW.aestronglyMeasurable.congr (hνG.mono eW),
    hWe, hl2 ▸ htop.lt_top, hl2 ▸ h0, fun x hx => ?_⟩
  have hml : Measurable (lmulM x : Mt k r → Mt k r) :=
    (continuous_mulM.comp (Continuous.prodMk (continuous_const (y := Matrix.of.symm x)) continuous_id)).measurable
  have hmp : MeasurePreserving (lmulM x) μG μG := ⟨hml, hμ.2.2.2 x hx⟩
  refine integral_congr_ae ((hmp.quasiMeasurePreserving.ae hfixG).mono fun g hg => ?_)
  exact congrArg (fun t => e (Matrix.of g) • t) hg

end GlobalTheory.BesselFixed
