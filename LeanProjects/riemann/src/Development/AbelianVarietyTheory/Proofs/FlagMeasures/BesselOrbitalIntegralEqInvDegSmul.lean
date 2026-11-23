import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOrbitOpNormIntegralFiniteOnCompactRegularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelUnitaryGroupOpNormPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselConstantBoundsOfGeTwoNPowFiveStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.OrbSchur

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
variable {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem isUnit_det {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det := by
  by_contra h
  have h1 := (GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r).1 g hg
  rw [Matrix.nonsing_inv_apply_not_isUnit _ h] at h1
  have h0 : opn (0 : Mat k r) = 0 := by simp [opn]
  linarith [h1.1, h1.2]

theorem continuousOn_matInv : ContinuousOn (fun g : Mat k r => g⁻¹) (GG k r) := by
  intro g hg
  refine (continuousAt_matrix_inv g ?_).continuousWithinAt
  rw [Ring.inverse_eq_inv']
  exact continuousAt_inv₀ (isUnit_det hg).ne_zero

theorem continuous_of : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) := continuous_id

theorem haar_ae {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) :
    ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ S := ae_iff.2 h.2.2.1

theorem aesm_of_continuousOn {X E : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [SecondCountableTopology X] [NormedAddCommGroup E] {μ : Measure X}
    {K : Set X} (hK : IsClosed K) (hμ : ∀ᵐ x ∂μ, x ∈ K) {f : X → E} (hf : ContinuousOn f K) :
    AEStronglyMeasurable f μ := by
  have := hf.aestronglyMeasurable (μ := μ) hK.measurableSet
  rwa [Measure.restrict_eq_self_of_ae_mem hμ] at this

theorem continuous_rankOneOperator : Continuous fun p : Wp × Wq => rk1 p.1 p.2 :=
  (ContinuousLinearMap.smulRightL ℂ Wq Wp).continuous₂.comp
    (((innerSL ℂ (E := Wq)).continuous.comp continuous_snd).prodMk continuous_fst)

theorem rankOneInnerOperator_smul_smul (c c' : ℂ) (a : Wp) (b : Wq) : rk1 (c • a) (c' • b) = (c * star c') • rk1 a b := by
  ext η
  simp [rankOneInnerOperator_apply, smul_smul, mul_comm, mul_left_comm]

theorem integral_prod_rankOneInnerOperator [CompleteSpace Wp] [CompleteSpace Wq] {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] {f : α → Wp}
    {g : β → Wq} (hf : Integrable f μ) (hg : Integrable g ν) :
    ∫ z, rk1 (f z.1) (g z.2) ∂μ.prod ν = rk1 (∫ x, f x ∂μ) (∫ y, g y ∂ν) := by
  have hg' : Integrable (fun y => innerSL ℂ (g y)) ν := (innerSL ℂ (E := Wq)).integrable_comp hg
  have h := integral_prod_bilin (ContinuousLinearMap.smulRightL ℂ Wq Wp).flip hf hg'
  have h2 : ∫ y, innerSL ℂ (g y) ∂ν = innerSL ℂ (∫ y, g y ∂ν) :=
    ContinuousLinearMap.integral_comp_commSL RCLike.conj_smul (innerSL ℂ (E := Wq)) hg
  rw [h2] at h
  exact h

theorem integrable_majorant (hG : IsClosedSub k r (GG k r)) {μG : Measure (Mt k r)}
    (hμ : IsHaarOn (GG k r) μG) {P : Measure (Mt k r × Mt k r)} [SFinite P]
    (hP : ∀ᵐ p ∂P, (Matrix.of p.1 : Mat k r) ∈ GG k r) {Φ : Mt k r × Mt k r → ℝ} (hΦ : Integrable Φ P)
    {A : ℝ} (hA : 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A) :
    Integrable (fun q : (Mt k r × Mt k r) × Mt k r =>
      Φ q.1 * opn (Matrix.of q.1.1 * Matrix.of q.2 : Mat k r) ^ (-A)) (P.prod μG) := by
  have := hμ.1
  have hc := (GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r).2.2.1
  have hm : Measurable fun x : Mt k r => opn (Matrix.of x : Mat k r) ^ (-A) :=
    (hc.comp continuous_of).measurable.pow_const _
  have hnn : ∀ x : Mat k r, 0 ≤ opn x ^ (-A) := fun x => Real.rpow_nonneg (opn_nonneg _) _
  have hi : Integrable (fun x : Mt k r => opn (Matrix.of x : Mat k r) ^ (-A)) μG :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => hnn _)).2
      (GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup k r _ μG A hG hμ hA)⟩
  have hl : ∀ s : Mat k r, Measurable (lmulM s : Mt k r → Mt k r) := fun s => by
    have : Continuous (lmulM s : Mt k r → Mt k r) := continuous_const.matrix_mul continuous_of
    exact this.measurable
  have hmul : Continuous fun q : (Mt k r × Mt k r) × Mt k r =>
      (Matrix.of q.1.1 * Matrix.of q.2 : Mat k r) :=
    Continuous.matrix_mul (continuous_fst.comp continuous_fst) continuous_snd
  have hms : AEStronglyMeasurable (fun q : (Mt k r × Mt k r) × Mt k r =>
      Φ q.1 * opn (Matrix.of q.1.1 * Matrix.of q.2 : Mat k r) ^ (-A)) (P.prod μG) :=
    hΦ.1.comp_fst.mul ((hc.comp hmul).measurable.pow_const _).aestronglyMeasurable
  rw [integrable_prod_iff hms]
  constructor
  · filter_upwards [hP] with p hp
    have hmp : MeasurePreserving (lmulM (Matrix.of p.1)) μG μG := ⟨hl _, hμ.2.2.2 _ hp⟩
    exact (hmp.integrable_comp_of_integrable hi).const_mul (Φ p)
  · refine (hΦ.norm.mul_const (∫ x, opn (Matrix.of x : Mat k r) ^ (-A) ∂μG)).congr ?_
    filter_upwards [hP] with p hp
    have h1 := integral_map (μ := μG) (hl (Matrix.of p.1)).aemeasurable
      (f := fun x : Mt k r => opn (Matrix.of x : Mat k r) ^ (-A)) hm.aestronglyMeasurable
    rw [hμ.2.2.2 _ hp] at h1
    rw [h1, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [norm_mul]
    rw [Real.norm_of_nonneg (hnn _)]
    rfl

theorem coef_mul_left {σ : Mat k r → (H →L[ℂ] H)} [CompleteSpace H] (hG : IsClosedSub k r (GG k r))
    (hσ : IsURepOn (GG k r) σ) (u v : H) {g x : Mat k r} (hg : g ∈ GG k r) (hx : x ∈ GG k r) :
    coef σ u v (g * x) = coef σ u (σ g⁻¹ v) x := by
  have hi := hG.2.2.2.2 g hg
  have hv : σ g (σ g⁻¹ v) = v := by
    have := hσ.1.2 g hg _ hi
    rw [Matrix.mul_nonsing_inv _ (isUnit_det hg), hσ.1.1] at this
    simpa using (congrArg (fun T : H →L[ℂ] H => T v) this).symm
  have hiso : ∀ a b : H, ⟪σ g a, σ g b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b =>
    (LinearIsometry.mk (σ g : H →ₗ[ℂ] H) (hσ.2.1 g hg)).inner_map_map a b
  unfold coef
  rw [hσ.1.2 g hg x hx, ← hiso (σ g⁻¹ v), hv]
  rfl

theorem coef_mul_right {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (u v : H)
    {g x : Mat k r} (hg : g ∈ GG k r) (hx : x ∈ GG k r) :
    coef σ (σ x u) v g = coef σ u v (g * x) := by
  unfold coef
  rw [hσ.1.2 g hg x hx]
  rfl

theorem continuousOn_coef {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (u v : H) :
    ContinuousOn (coef σ u v) (GG k r) :=
  continuousOn_const.inner (hσ.2.2 u)

theorem DD_stable {σ : Mat k r → (H →L[ℂ] H)} (hG : IsClosedSub k r (GG k r))
    (hσ : IsURepOn (GG k r) σ) (w : H) : ∀ g ∈ GG k r, ∀ v ∈ (DD σ w : Set H), σ g v ∈ (DD σ w : Set H) := by
  intro g hg v hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, hh, rfl⟩ := hx
    have := mem_DD σ w (hG.2.2.2.1 g hg h hh)
    rw [hσ.1.2 g hg h hh] at this
    exact this
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact (DD σ w).add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact (DD σ w).smul_mem c hx

theorem integral_coef_translate {σ : Mat k r → (H →L[ℂ] H)} [CompleteSpace H]
    (hG : IsClosedSub k r (GG k r)) (hσ : IsURepOn (GG k r) σ) {μG : Measure (Mt k r)}
    (hμ : IsHaarOn (GG k r) μG) {d : ℝ} (hS : SchurH μG σ d) {w : H} (hw : ‖w‖ = 1) (v v' : H)
    {s t : Mat k r} (hs : s ∈ GG k r) (ht : t ∈ GG k r) :
    ∫ x, coef σ w v (s * Matrix.of x) * star (coef σ w v' (t * Matrix.of x)) ∂μG =
      (d : ℂ)⁻¹ * coef σ v' v (s * t⁻¹) := by
  have h := (hS.2 w (σ s⁻¹ v) w (σ t⁻¹ v')).2
  rw [coef_mul_left hG hσ v' v hs (hG.2.2.2.2 t ht)]
  rw [inner_self_eq_norm_sq_to_K, hw] at h
  rw [integral_congr_ae (g := fun x => coef σ w (σ s⁻¹ v) (Matrix.of x) *
    star (coef σ w (σ t⁻¹ v') (Matrix.of x))), h]
  · simp [coef, div_eq_inv_mul]
  · filter_upwards [haar_ae hμ] with x hx
    rw [coef_mul_left hG hσ w v hs hx, coef_mul_left hG hσ w v' ht hx]

theorem rpow_bound (hG : IsClosedSub k r (GG k r)) {y y' : Mat k r} (hy : y ∈ GG k r) (hy' : y' ∈ GG k r)
    {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) :
    opn y ^ (-a) * opn y' ^ (-a) ≤ opn (y * y'⁻¹) ^ (-b) * opn y ^ (-(a - b)) := by
  obtain ⟨hN, hmul, -⟩ := GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties k r
  have h1 := (hN y hy).2
  have h2 := (hN y' hy').2
  have h3 := (hN _ (hG.2.2.2.1 y hy _ (hG.2.2.2.2 y' hy'))).2
  have h4 : opn (y * y'⁻¹) ≤ opn y * opn y' := by
    have := hmul y y'⁻¹
    rwa [(hN y' hy').1] at this
  have h5 : (opn y * opn y') ^ (-b) ≤ opn (y * y'⁻¹) ^ (-b) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) h4 (by linarith)
  have h6 : opn y' ^ (-a) ≤ opn y' ^ (-b) := Real.rpow_le_rpow_of_exponent_le h2 (by linarith)
  have h7 : opn y ^ (-a) = opn y ^ (-b) * opn y ^ (-(a - b)) := by
    rw [← Real.rpow_add (by linarith)]; congr 1; ring
  rw [Real.mul_rpow (by linarith) (by linarith)] at h5
  have p1 : 0 ≤ opn y ^ (-b) := Real.rpow_nonneg (by linarith) _
  have p2 : 0 ≤ opn y ^ (-(a - b)) := Real.rpow_nonneg (by linarith) _
  calc opn y ^ (-a) * opn y' ^ (-a) = (opn y ^ (-b) * opn y' ^ (-a)) * opn y ^ (-(a - b)) := by
        rw [h7]; ring
    _ ≤ (opn y ^ (-b) * opn y' ^ (-b)) * opn y ^ (-(a - b)) := by gcongr
    _ ≤ _ := by gcongr

theorem integrable_triple {σ : Mat k r → (H →L[ℂ] H)} {w : H} {a : ℝ} {μG : Measure (Mt k r)} {d : ℝ}
    (hstd : Std σ w a μG d) {z z' : Fin (2 * r + k + 1) → ℂ} {μS μS' : Measure (Mt k r)}
    (hz : inWb k r z) (hT : 0 < Tz k r z) (hz' : inWb k r z') (hT' : 0 < Tz k r z')
    (hS : IsHaarOn (Sset k r z) μS) (hS' : IsHaarOn (Sset k r z') μS')
    {f : Mat k r → Wp} {f' : Mat k r → Wq} (hf : ContinuousOn f (Sset k r z))
    (hf' : ContinuousOn f' (Sset k r z')) {M M' : ℝ} (hM : ∀ s ∈ Sset k r z, ‖f s‖ ≤ M)
    (hM' : ∀ s ∈ Sset k r z', ‖f' s‖ ≤ M') {w₀ w₀' : H} (hw₀ : w₀ ∈ DD σ w) (hw₀' : w₀' ∈ DD σ w)
    {γ : Mat k r} (hγ : γ ∈ Greg k r z z') :
    Integrable (fun q : (Mt k r × Mt k r) × Mt k r =>
      (coef σ w w₀ (Matrix.of q.1.1 * Matrix.of q.2) *
        star (coef σ w w₀' (Matrix.of q.1.2 * γ⁻¹ * Matrix.of q.2))) •
        rk1 (f (Matrix.of q.1.1)) (f' (Matrix.of q.1.2))) ((μS.prod μS').prod μG) := by
  obtain ⟨hk, hσ, -, hw, hμ, -, ha, hdec, -⟩ := hstd
  have := hμ.1
  have := hS.1
  have := hS'.1
  obtain ⟨hG, -, -, hSc, -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  obtain ⟨-, -, -, hSc', -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z' hz' hT'
  have hnum := (GlobalTheory.T.bessel_constant_bounds_of_ge_two_n_pow_five k r a hk ha).2
  set b : ℝ := 2 * ((2 * (r ^ 2 + r + 1) : ℕ) : ℝ) * (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2) + 1 with hb
  have hb0 : 0 ≤ b := by positivity
  have hn0 : 0 ≤ 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  obtain ⟨-, Φ, hΦ, hΦb⟩ := GlobalTheory.T.besselOrbitOpNormIntegral_finite_on_compact_regular k r z z' μS μS' b {γ} hz hz' hT hT' hS hS' (by linarith)
    isCompact_singleton (Set.singleton_subset_iff.2 hγ)
  have hγG : γ ∈ GG k r := hγ.1
  have hγi := hG.2.2.2.2 γ hγG
  have hwD : w ∈ DD σ w := by
    have := mem_DD σ w hG.2.2.1
    rwa [hσ.1.1] at this
  obtain ⟨C, hC⟩ := hdec w hwD w₀ hw₀
  obtain ⟨C', hC'⟩ := hdec w hwD w₀' hw₀'
  have hP1 : ∀ᵐ p ∂(μS.prod μS'), (Matrix.of p.1 : Mat k r) ∈ Sset k r z :=
    Measure.quasiMeasurePreserving_fst.ae (haar_ae hS)
  have hP2 : ∀ᵐ p ∂(μS.prod μS'), (Matrix.of p.2 : Mat k r) ∈ Sset k r z' :=
    Measure.quasiMeasurePreserving_snd.ae (haar_ae hS')
  have hK : ∀ᵐ q ∂((μS.prod μS').prod μG), q ∈ {q : (Mt k r × Mt k r) × Mt k r |
      ((Matrix.of q.1.1 : Mat k r) ∈ Sset k r z ∧ (Matrix.of q.1.2 : Mat k r) ∈ Sset k r z') ∧
        (Matrix.of q.2 : Mat k r) ∈ GG k r} :=
    (Measure.quasiMeasurePreserving_fst.ae (hP1.and hP2)).and
      (Measure.quasiMeasurePreserving_snd.ae (haar_ae hμ))
  have c1 : Continuous fun q : (Mt k r × Mt k r) × Mt k r => (Matrix.of q.1.1 : Mat k r) :=
    continuous_of.comp (continuous_fst.comp continuous_fst)
  have c2 : Continuous fun q : (Mt k r × Mt k r) × Mt k r => (Matrix.of q.1.2 : Mat k r) :=
    continuous_of.comp (continuous_snd.comp continuous_fst)
  have c3 : Continuous fun q : (Mt k r × Mt k r) × Mt k r => (Matrix.of q.2 : Mat k r) :=
    continuous_of.comp continuous_snd
  have hmaj := (integrable_majorant hG hμ (hP1.mono fun p hp => hSc.1 hp) hΦ (A := a - b)
    (by linarith)).const_mul (|C| * |C'| * (M * M'))
  have hcl : IsClosed {q : (Mt k r × Mt k r) × Mt k r |
      ((Matrix.of q.1.1 : Mat k r) ∈ Sset k r z ∧ (Matrix.of q.1.2 : Mat k r) ∈ Sset k r z') ∧
        (Matrix.of q.2 : Mat k r) ∈ GG k r} :=
    ((hSc.2.1.preimage c1).inter (hSc'.2.1.preimage c2)).inter (hG.2.1.preimage c3)
  refine hmaj.mono' (aesm_of_continuousOn hcl hK ?_) ?_
  · exact (((continuousOn_coef hσ w w₀).comp (c1.matrix_mul c3).continuousOn
        fun q hq => hG.2.2.2.1 _ (hSc.1 hq.1.1) _ hq.2).mul ((continuousOn_coef hσ w w₀').comp
        ((c2.matrix_mul continuous_const).matrix_mul c3).continuousOn
        fun q hq => hG.2.2.2.1 _ (hG.2.2.2.1 _ (hSc'.1 hq.1.2) _ hγi) _ hq.2).star).smul
      (continuous_rankOneOperator.comp_continuousOn ((hf.comp c1.continuousOn fun q hq => hq.1.1).prodMk
        (hf'.comp c2.continuousOn fun q hq => hq.1.2)))
  · filter_upwards [hK] with q hq
    obtain ⟨⟨hs, hs'⟩, hx⟩ := hq
    have hb1 := hΦb γ rfl q.1 hs hs'
    have e : (Matrix.of (act2 γ q.1) : Mat k r) = Matrix.of q.1.1 * γ * (Matrix.of q.1.2)⁻¹ := rfl
    rw [e] at hb1
    generalize (Matrix.of q.1.1 : Mat k r) = s at *
    generalize (Matrix.of q.1.2 : Mat k r) = s' at *
    generalize (Matrix.of q.2 : Mat k r) = x at *
    have hy := hG.2.2.2.1 _ (hSc.1 hs) _ hx
    have hy' := hG.2.2.2.1 _ (hG.2.2.2.1 _ (hSc'.1 hs') _ hγi) _ hx
    have hr := rpow_bound hG hy hy' hb0 (show b ≤ a by linarith)
    have e2 : s * x * (s' * γ⁻¹ * x)⁻¹ = s * γ * s'⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det hγG),
        Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_det hx), Matrix.mul_assoc]
    rw [e2] at hr
    have p1 : 0 ≤ opn (s * x) ^ (-a) := Real.rpow_nonneg (opn_nonneg _) _
    have p2 : 0 ≤ opn (s' * γ⁻¹ * x) ^ (-a) := Real.rpow_nonneg (opn_nonneg _) _
    have p3 : 0 ≤ opn (s * x) ^ (-(a - b)) := Real.rpow_nonneg (opn_nonneg _) _
    have q1 : ‖coef σ w w₀ (s * x)‖ ≤ |C| * opn (s * x) ^ (-a) :=
      (hC _ hy).trans (mul_le_mul_of_nonneg_right (le_abs_self _) p1)
    have q2 : ‖coef σ w w₀' (s' * γ⁻¹ * x)‖ ≤ |C'| * opn (s' * γ⁻¹ * x) ^ (-a) :=
      (hC' _ hy').trans (mul_le_mul_of_nonneg_right (le_abs_self _) p2)
    have m1 := hM s hs
    have m2 := hM' s' hs'
    have m3 : 0 ≤ M := (norm_nonneg _).trans m1
    have m4 : 0 ≤ M' := (norm_nonneg _).trans m2
    rw [norm_smul, norm_mul, norm_star, norm_rankOneInnerOperator]
    calc _ ≤ (|C| * opn (s * x) ^ (-a)) * (|C'| * opn (s' * γ⁻¹ * x) ^ (-a)) * (M * M') :=
          mul_le_mul (mul_le_mul q1 q2 (norm_nonneg _) ((norm_nonneg _).trans q1))
            (mul_le_mul m1 m2 (norm_nonneg _) m3) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (mul_nonneg ((norm_nonneg _).trans q1) ((norm_nonneg _).trans q2))
      _ = |C| * |C'| * (M * M') * (opn (s * x) ^ (-a) * opn (s' * γ⁻¹ * x) ^ (-a)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hr.trans (mul_le_mul_of_nonneg_right hb1 p3))
          (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg m3 m4))

end GlobalTheory.SgInf.OrbSchur

open GlobalTheory.SgInf.OrbSchur in

theorem GlobalTheory.SgInf.OO_eq_inv_deg_smul_Iint : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ w₀ ∈ DD σ w, ∀ w₀' ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∀ γ ∈ Greg k r z z', Integrable (fun p : Mt k r × Mt k r => coef σ w₀' w₀ (Matrix.of (act2 γ p)) • rk1 (PiS (psiGen k r z c) π (Matrix.of p.1)⁻¹ ξ) (PiS (psiGen k r z' c') π' (Matrix.of p.2)⁻¹ ξ')) (μS.prod μS') ∧ Integrable (fun x : Mt k r => rk1 ((Afun (psiGen k r z c) π μS σ w w₀ ξ) (Matrix.of x)) ((Afun (psiGen k r z' c') π' μS' σ w w₀' ξ') (γ⁻¹ * Matrix.of x))) μG ∧ OO μG (Afun (psiGen k r z c) π μS σ w w₀ ξ) (Afun (psiGen k r z' c') π' μS' σ w w₀' ξ') γ = (d : ℂ)⁻¹ • Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ w₀' w₀ ξ ξ' γ := by
  intro k r H _ _ _ Wp _ _ _ _ Wq _ _ _ _ σ w a μG d z c π μS z' c' π' μS' hstd hsd hsd' w₀ hw₀ w₀' hw₀'
    ξ ξ' γ hγ
  have hD := GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hstd hsd
  have hD' := GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z' c' π' μS' hstd hsd'
  obtain ⟨hz, hT, hπ, hS, -⟩ := hsd
  obtain ⟨hz', hT', hπ', hS', -⟩ := hsd'
  obtain ⟨hG, -, -, hSc, -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  obtain ⟨-, -, -, hSc', -⟩ := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z' hz' hT'
  obtain ⟨-, hP, -⟩ := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ
  obtain ⟨-, hP', -⟩ := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z' c' π' hz' hT' hπ'
  have hI := integrable_triple hstd hz hT hz' hT' hS hS'
    (f := fun s => PiS (psiGen k r z c) π s⁻¹ ξ) (f' := fun s => PiS (psiGen k r z' c') π' s⁻¹ ξ')
    ((hP.2.2 ξ).comp (continuousOn_matInv.mono hSc.1) fun s hs => hSc.2.2.2.2 s hs)
    ((hP'.2.2 ξ').comp (continuousOn_matInv.mono hSc'.1) fun s hs => hSc'.2.2.2.2 s hs)
    (fun s hs => (hP.2.1 _ (hSc.2.2.2.2 s hs) ξ).le) (fun s hs => (hP'.2.1 _ (hSc'.2.2.2.2 s hs) ξ').le)
    hw₀ hw₀' hγ
  obtain ⟨hk, hσ, -, hw, hμ, hSch, ha, hdec, -⟩ := hstd
  have := hμ.1
  have := hS.1
  have := hS'.1
  have hγG : γ ∈ GG k r := hγ.1
  have hγi := hG.2.2.2.2 γ hγG
  have hst := DD_stable hG hσ w
  have hwD : w ∈ DD σ w := by
    have := mem_DD σ w hG.2.2.1
    rwa [hσ.1.1] at this
  have hP12 : ∀ᵐ p ∂(μS.prod μS'), (Matrix.of p.1 : Mat k r) ∈ Sset k r z ∧
      (Matrix.of p.2 : Mat k r) ∈ Sset k r z' :=
    (Measure.quasiMeasurePreserving_fst.ae (haar_ae hS)).and
      (Measure.quasiMeasurePreserving_snd.ae (haar_ae hS'))
  set F : (Mt k r × Mt k r) × Mt k r → (Wq →L[ℂ] Wp) := fun q =>
      (coef σ w w₀ (Matrix.of q.1.1 * Matrix.of q.2) *
        star (coef σ w w₀' (Matrix.of q.1.2 * γ⁻¹ * Matrix.of q.2))) •
        rk1 (PiS (psiGen k r z c) π (Matrix.of q.1.1)⁻¹ ξ) (PiS (psiGen k r z' c') π' (Matrix.of q.1.2)⁻¹ ξ')
    with hF
  have hL : (fun p => ∫ x, F (p, x) ∂μG) =ᵐ[μS.prod μS'] fun p => (d : ℂ)⁻¹ •
      (coef σ w₀' w₀ (Matrix.of (act2 γ p)) • rk1 (PiS (psiGen k r z c) π (Matrix.of p.1)⁻¹ ξ)
        (PiS (psiGen k r z' c') π' (Matrix.of p.2)⁻¹ ξ')) := by
    filter_upwards [hP12] with p hp
    simp only [hF]
    rw [integral_smul_const, integral_coef_translate hG hσ hμ hSch hw w₀ w₀' (hSc.1 hp.1)
      (hG.2.2.2.1 _ (hSc'.1 hp.2) _ hγi), Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ (isUnit_det hγG), ← Matrix.mul_assoc, mul_smul]
    rfl
  have hR : (fun x => ∫ p, F (p, x) ∂(μS.prod μS')) =ᵐ[μG] fun x =>
      rk1 ((Afun (psiGen k r z c) π μS σ w w₀ ξ) (Matrix.of x))
        ((Afun (psiGen k r z' c') π' μS' σ w w₀' ξ') (γ⁻¹ * Matrix.of x)) := by
    filter_upwards [haar_ae hμ] with x hx
    have hx' := hG.2.2.2.1 _ hγi _ hx
    have i1 := (hD _ hst hdec _ (hst _ hx w hwD) w₀ hw₀).1
    have i2 := (hD' _ hst hdec _ (hst _ hx' w hwD) w₀' hw₀').1
    unfold Afun be
    rw [ContinuousLinearMap.integral_apply i1, ContinuousLinearMap.integral_apply i2,
      ← integral_prod_rankOneInnerOperator (i1.apply_continuousLinearMap ξ) (i2.apply_continuousLinearMap ξ')]
    refine integral_congr_ae ?_
    filter_upwards [hP12] with p hp
    simp only [hF, _root_.smul_apply]
    rw [rankOneInnerOperator_smul_smul, coef_mul_right hσ _ _ (hSc.1 hp.1) hx, coef_mul_right hσ _ _ (hSc'.1 hp.2) hx',
      Matrix.mul_assoc]
  have hd : (d : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.2 hSch.1.ne')
  refine ⟨(integrable_smul_iff hd _).1 (hI.integral_prod_left.congr hL),
    hI.integral_prod_right.congr hR, ?_⟩
  unfold OO Iint
  rw [← integral_congr_ae hR, ← integral_smul, ← integral_congr_ae hL]
  exact (integral_integral_swap (f := fun p x => F (p, x)) hI).symm
