import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KMapLowestKTypeSubspaceEqScalar

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

private lemma hs_mul_sub_one_comm_of_mem_Kset {n : ℕ} (ε : Fin n → Bool) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Kset ε) (y : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (k * y - 1) = Formalism.REAL.hs (y * k - 1) := by
  have hu : k ∈ Matrix.unitaryGroup (Fin n) ℂ := hk.1
  have h1 : k * star k = 1 := Matrix.mem_unitaryGroup_iff.mp hu
  have h2 : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  have e1 : k * y - 1 = k * (y - star k) := by rw [mul_sub, h1]
  have e2 : y * k - 1 = (y - star k) * k := by rw [sub_mul, h2]
  have hinv := (hSBall n ε).2 (y - star k) k hk
  rw [e1, e2, hinv.1, hinv.2]

private lemma norm_apply_sq_le_hs {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖A i j‖ ^ 2 ≤ Formalism.REAL.hs A := by
  unfold Formalism.REAL.hs
  calc ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

private lemma contDiff_hs_sub_one {n : ℕ} :
    ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => Formalism.REAL.hs (y - 1)) := by
  unfold Formalism.REAL.hs
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have hsub : ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => y - 1) :=
    contDiff_id.sub contDiff_const
  have hent : ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => (y - 1) i j) :=
    (contDiff_apply_apply ℝ ℂ i j).comp hsub
  exact (contDiff_norm_sq ℝ).comp hent

theorem exists_conjInvariant_bump (n : ℕ) (ε : Fin n → Bool) (U : Set (UJ ε))
    (hU : U ∈ nhds (1 : UJ ε)) :
    ∃ a : Matrix (Fin n) (Fin n) ℂ → ℝ, ContDiff ℝ ∞ a ∧ (∀ y, 0 ≤ a y) ∧ a 1 ≠ 0 ∧
      HasCompactSupport (fun g : UJ ε => a (umat g)) ∧ (∀ g : UJ ε, a (umat g) ≠ 0 → g ∈ U) ∧
      ∀ k ∈ Kset ε, ∀ y, a (k * y) = a (y * k) := by
  obtain ⟨hemb, -⟩ := uJEmb n ε
  have hU' : U ∈ Filter.comap (fun g : UJ ε => umat g) (nhds (umat (1 : UJ ε))) := by
    rw [← hemb.isInducing.nhds_eq_comap]; exact hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU'
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
  have hone : umat (1 : UJ ε) = 1 := rfl
  have hqc : Continuous (fun y : Matrix (Fin n) (Fin n) ℂ => Formalism.REAL.hs (y - 1)) :=
    contDiff_hs_sub_one.continuous
  have hball : ∀ y : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.hs (y - 1) < r ^ 2 →
      y ∈ Metric.ball (umat (1 : UJ ε)) r := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm, hone, Matrix.norm_lt_iff hr]
    intro i j
    exact lt_of_pow_lt_pow_left₀ 2 hr.le ((norm_apply_sq_le_hs (y - 1) i j).trans_lt hy)
  have hcb : {y : Matrix (Fin n) (Fin n) ℂ | Formalism.REAL.hs (y - 1) ≤ r ^ 2} ⊆
      Metric.closedBall (1 : Matrix (Fin n) (Fin n) ℂ) r := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm, Matrix.norm_le_iff hr.le]
    intro i j
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr.le two_ne_zero).mp
      ((norm_apply_sq_le_hs (y - 1) i j).trans hy)
  have hr2 : 0 < r ^ 2 := by positivity
  refine ⟨fun y => Real.smoothTransition ((r ^ 2 - Formalism.REAL.hs (y - 1)) / r ^ 2), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · exact Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub contDiff_hs_sub_one).div_const _)
  · intro y
    exact Real.smoothTransition.nonneg _
  · have h0 : Formalism.REAL.hs ((1 : Matrix (Fin n) (Fin n) ℂ) - 1) = 0 := by
      simp [Formalism.REAL.hs]
    simp only [h0, sub_zero, div_self hr2.ne']
    rw [Real.smoothTransition.one_of_one_le le_rfl]
    exact one_ne_zero
  · have hclosed : IsClosed {y : Matrix (Fin n) (Fin n) ℂ | Formalism.REAL.hs (y - 1) ≤ r ^ 2} :=
      isClosed_le hqc continuous_const
    haveI : ProperSpace (Matrix (Fin n) (Fin n) ℂ) :=
      inferInstanceAs (ProperSpace (Fin n → Fin n → ℂ))
    have hK : IsCompact {y : Matrix (Fin n) (Fin n) ℂ | Formalism.REAL.hs (y - 1) ≤ r ^ 2} :=
      (isCompact_closedBall (1 : Matrix (Fin n) (Fin n) ℂ) r).of_isClosed_subset hclosed hcb
    refine HasCompactSupport.intro' (hemb.isCompact_preimage hK)
      (hclosed.preimage hemb.continuous) ?_
    intro g hg
    simp only [Set.mem_preimage, Set.mem_setOf_eq, not_le] at hg
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hr2.le)
  · intro g hg
    apply hVU
    apply hrV
    apply hball
    by_contra h
    push_neg at h
    exact hg (Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hr2.le))
  · intro k hk y
    simp only [hs_mul_sub_one_comm_of_mem_Kset ε hk y]

theorem exists_smooth_fix_lowKSub : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∃ α : Matrix (Fin n) (Fin n) ℂ → ℂ, SmoothOnG ε α ∧ HasCompactSupport (fun g : UJ ε => α (umat g)) ∧ ∀ s ∈ lowKSub ε lam σ, ∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, s⟫_ℂ := by
  intro n ε lam H _ _ _ σ hσ hS
  obtain ⟨hemb, hrange⟩ := uJEmb n ε
  have hσ' := hσ
  obtain ⟨⟨hσ1, hm⟩, -, hcont⟩ := hσ'
  have hS' := hS
  obtain ⟨-, -, -, ⟨s0, hs0S, hs0, -⟩, -⟩ := hS'
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hmul : ∀ x y : UJ ε, umat (x * y) = umat x * umat y := fun _ _ => rfl
  have hone : umat (1 : UJ ε) = 1 := rfl
  have hcontσ : ∀ v : H, Continuous (fun g : UJ ε => σ (umat g) v) := fun v =>
    (hcont v).comp_continuous hemb.continuous hmem
  have hs0pos : 0 < ‖s0‖ := norm_pos_iff.mpr hs0
  let U : Set (UJ ε) := {g | ‖σ (umat g) s0 - s0‖ < ‖s0‖ / 2}
  have hU : U ∈ nhds (1 : UJ ε) := by
    have h1 : σ (umat (1 : UJ ε)) s0 = s0 := by rw [hone, hσ1]; rfl
    have hpre := ((hcontσ s0).continuousAt (x := 1)).preimage_mem_nhds
      (Metric.ball_mem_nhds (σ (umat (1 : UJ ε)) s0) (half_pos hs0pos))
    refine Filter.mem_of_superset hpre ?_
    intro g hg
    have hg' : dist (σ (umat g) s0) (σ (umat (1 : UJ ε)) s0) < ‖s0‖ / 2 := hg
    rw [h1, dist_eq_norm] at hg'
    exact hg'
  obtain ⟨a, ha_sm, ha_nn, ha1, ha_cpt, ha_supp, ha_conj⟩ := exists_conjInvariant_bump n ε U hU
  haveI : (muG ε).IsMulRightInvariant := ⟨fun g => unimodular n ε g⟩
  have hAc : Continuous (fun g : UJ ε => (a (umat g) : ℂ)) :=
    Complex.continuous_ofReal.comp (ha_sm.continuous.comp hemb.continuous)
  have hAcpt : HasCompactSupport (fun g : UJ ε => (a (umat g) : ℂ)) :=
    ha_cpt.comp_left Complex.ofReal_zero
  let F : H → UJ ε → H := fun v g => (a (umat g) : ℂ) • σ (umat g) v
  have hFi : ∀ v, Integrable (F v) (muG ε) := fun v =>
    (hAc.smul (hcontσ v)).integrable_of_hasCompactSupport hAcpt.smul_right
  let T : lowKSub ε lam σ →ₗ[ℂ] H :=
    { toFun := fun s => ∫ g, F s g ∂(muG ε)
      map_add' := fun x y => by
        simp only [F, Submodule.coe_add, map_add, smul_add]
        exact integral_add (hFi x) (hFi y)
      map_smul' := fun c x => by
        simp only [F, Submodule.coe_smul, map_smul, RingHom.id_apply]
        rw [← integral_smul]
        congr 1
        funext g
        rw [smul_comm] }
  have hK : ∀ k ∈ Kset ε, ∃ kk : UJ ε, umat kk = k := by
    intro k hk
    have hk' : k ∈ Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
        Matrix (Fin n) (Fin n) ℂ)) := hrange ▸ (kFacts n ε).1 k hk
    obtain ⟨kk, hkk⟩ := hk'
    exact ⟨kk, hkk⟩
  have hconj : ∀ (kk : UJ ε) (f : UJ ε → H),
      ∫ h, f (kk * h * kk⁻¹) ∂(muG ε) = ∫ g, f g ∂(muG ε) := by
    intro kk f
    calc ∫ h, f (kk * h * kk⁻¹) ∂(muG ε) = ∫ h, (fun x => f (kk * x)) (h * kk⁻¹) ∂(muG ε) := by
          congr 1
          funext h
          rw [mul_assoc]
      _ = ∫ h, f (kk * h) ∂(muG ε) := integral_mul_right_eq_self (fun x => f (kk * x)) kk⁻¹
      _ = ∫ g, f g ∂(muG ε) := integral_mul_left_eq_self f kk
  have hT : ∀ k ∈ Kset ε, ∀ s s' : lowKSub ε lam σ, (s' : H) = σ k s → T s' = σ k (T s) := by
    intro k hk s s' hss
    obtain ⟨kk, rfl⟩ := hK k hk
    show ∫ g, F s' g ∂(muG ε) = σ (umat kk) (∫ g, F s g ∂(muG ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (hFi s), ← hconj kk (F s')]
    congr 1
    funext h
    show (a (umat (kk * h * kk⁻¹)) : ℂ) • σ (umat (kk * h * kk⁻¹)) (s' : H) =
      σ (umat kk) ((a (umat h) : ℂ) • σ (umat h) (s : H))
    have ha : a (umat (kk * h * kk⁻¹)) = a (umat h) := by
      have e : umat (kk * h * kk⁻¹) = umat kk * (umat h * umat kk⁻¹) := by
        rw [hmul, hmul, mul_assoc]
      rw [e, ha_conj _ hk, ← hmul, ← hmul, inv_mul_cancel_right]
    have e1 := hm _ (hmem (kk * h * kk⁻¹)) _ (hmem kk)
    rw [← hmul, show kk * h * kk⁻¹ * kk = kk * h by group] at e1
    have e2 := hm _ (hmem kk) _ (hmem h)
    rw [← hmul] at e2
    have hs : σ (umat (kk * h * kk⁻¹)) (σ (umat kk) s) = σ (umat kk) (σ (umat h) s) := by
      calc σ (umat (kk * h * kk⁻¹)) (σ (umat kk) s)
          = ((σ (umat (kk * h * kk⁻¹))).comp (σ (umat kk))) s := rfl
        _ = σ (umat (kk * h)) s := by rw [← e1]
        _ = ((σ (umat kk)).comp (σ (umat h))) s := by rw [e2]
        _ = σ (umat kk) (σ (umat h) s) := rfl
    rw [ha, hss, hs, map_smul]
  obtain ⟨c, hc⟩ := KMapInto.kMap_lowKSub_scalar n ε lam H σ hσ hS T hT
  have hinner : ∀ (s : lowKSub ε lam σ) (u : H),
      ∫ g, (a (umat g) : ℂ) * ⟪u, σ (umat g) (s : H)⟫_ℂ ∂(muG ε) = ⟪u, T s⟫_ℂ := by
    intro s u
    show _ = ⟪u, ∫ g, F s g ∂(muG ε)⟫_ℂ
    rw [← integral_inner (hFi s)]
    simp only [F, inner_smul_right]
  have hc0 : c ≠ 0 := by
    intro hc0
    have h0 := hinner ⟨s0, hs0S⟩ s0
    rw [hc, hc0, zero_smul, inner_zero_right] at h0
    have hre : ∀ g ∈ U, 0 < (⟪s0, σ (umat g) s0⟫_ℂ).re := by
      intro g hg
      have hg' : ‖σ (umat g) s0 - s0‖ < ‖s0‖ / 2 := hg
      have e : ⟪s0, σ (umat g) s0⟫_ℂ = ⟪s0, s0⟫_ℂ + ⟪s0, σ (umat g) s0 - s0⟫_ℂ := by
        rw [inner_sub_right]; ring
      have h1 : (⟪s0, s0⟫_ℂ).re = ‖s0‖ ^ 2 := by
        have := inner_self_eq_norm_sq (𝕜 := ℂ) s0
        simpa using this
      have h2 : |(⟪s0, σ (umat g) s0 - s0⟫_ℂ).re| ≤ ‖s0‖ * ‖σ (umat g) s0 - s0‖ :=
        (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
      rw [e, Complex.add_re, h1]
      have h3 := neg_abs_le (⟪s0, σ (umat g) s0 - s0⟫_ℂ).re
      nlinarith [mul_lt_mul_of_pos_left hg' hs0pos, pow_pos hs0pos 2]
    let φ : UJ ε → ℝ := fun g => a (umat g) * (⟪s0, σ (umat g) s0⟫_ℂ).re
    have hφc : Continuous φ :=
      (ha_sm.continuous.comp hemb.continuous).mul
        (Complex.continuous_re.comp (continuous_const.inner (hcontσ s0)))
    have hφcpt : HasCompactSupport φ := ha_cpt.mul_right
    have hφnn : 0 ≤ φ := by
      intro g
      by_cases hg : a (umat g) = 0
      · simp [φ, hg]
      · exact mul_nonneg (ha_nn _) (hre g (ha_supp g hg)).le
    have hφ1 : φ 1 ≠ 0 := by
      show a (umat (1 : UJ ε)) * (⟪s0, σ (umat (1 : UJ ε)) s0⟫_ℂ).re ≠ 0
      rw [hone, hσ1, ContinuousLinearMap.one_apply]
      have h1 : (⟪s0, s0⟫_ℂ).re = ‖s0‖ ^ 2 := by
        have := inner_self_eq_norm_sq (𝕜 := ℂ) s0
        simpa using this
      rw [h1]
      exact mul_ne_zero ha1 (pow_pos hs0pos 2).ne'
    have hpos := hφc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := muG ε) hφcpt hφnn hφ1
    have hint : Integrable (fun g : UJ ε => (a (umat g) : ℂ) * ⟪s0, σ (umat g) s0⟫_ℂ) (muG ε) :=
      (hAc.mul (continuous_const.inner (hcontσ s0))).integrable_of_hasCompactSupport
        hAcpt.mul_right
    have hre_int := integral_re hint
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at hre_int
    have h0' : (∫ g, (a (umat g) : ℂ) * ⟪s0, σ (umat g) s0⟫_ℂ ∂(muG ε)).re = 0 := by
      rw [show ((⟨s0, hs0S⟩ : lowKSub ε lam σ) : H) = s0 from rfl] at h0
      rw [h0, Complex.zero_re]
    have : ∫ g, φ g ∂(muG ε) = 0 := by rw [← h0', ← hre_int]
    linarith
  refine ⟨fun y => c⁻¹ * (a y : ℂ), ?_, ?_, ?_⟩
  · intro g₀ _
    refine ⟨Set.univ, fun y => c⁻¹ * (a y : ℂ), isOpen_univ, Set.mem_univ _, ?_,
      fun _ _ _ => rfl⟩
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp ha_sm)).contDiffOn
  · exact hAcpt.mul_left
  · intro s hs u
    have h : ∫ g, (a (umat g) : ℂ) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = c * ⟪u, s⟫_ℂ := by
      have := hinner ⟨s, hs⟩ u
      rw [hc, inner_smul_right] at this
      exact this
    calc ∫ g, c⁻¹ * (a (umat g) : ℂ) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε)
        = c⁻¹ * ∫ g, (a (umat g) : ℂ) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
          rw [← integral_const_mul]
          congr 1
          funext g
          ring
      _ = ⟪u, s⟫_ℂ := by
          rw [h, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

end GlobalTheory
