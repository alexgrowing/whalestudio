import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalTriangular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagOfBlockTriangularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfIsotropicBlocksStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableUnitaryLeviBlockMapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsConjGaugeInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingWithDensity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarComplexGLMatricesConjAndSingularNull
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIsotropicFlagSelfAdjointLeviIffBlockStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocSizeBlocks
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagStabilizerMulInvLeviComponentMemUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviChartMapHaarCarriedInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadialMapUnitaryLeviBlockProductStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptoticStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebraIsotropicFlagSelfAdjointLevi

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

noncomputable section

namespace GlobalTheory.LeviIso.Chart

def twist {j : ℕ} (p : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ →+* ℂ) (x : Fin j → Fin j → ℂ) : Fin j → Fin j → ℂ :=
  fun r s => (p * (Matrix.of x).map τ * p⁻¹) r s

theorem of_twist {j : ℕ} (p : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ →+* ℂ) (x : Fin j → Fin j → ℂ) :
    Matrix.of (twist p τ x) = p * (Matrix.of x).map τ * p⁻¹ := rfl

variable {j : ℕ} {p : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ →+* ℂ}

theorem norm_tau (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) (z : ℂ) : ‖τ z‖ = ‖z‖ := by
  rcases hτ with rfl | rfl <;> simp

theorem tau_tau (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) (z : ℂ) : τ (τ z) = z := by
  rcases hτ with rfl | rfl <;> simp

theorem det_map_tau (x : Matrix (Fin j) (Fin j) ℂ) : (x.map τ).det = τ x.det := by
  rw [RingHom.map_det]; rfl

theorem det_twist (hp : p.det ≠ 0) (x : Fin j → Fin j → ℂ) :
    (Matrix.of (twist p τ x)).det = τ (Matrix.of x).det := by
  rw [of_twist, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
    Matrix.mul_nonsing_inv _ (Ne.isUnit hp), Matrix.det_one, one_mul, det_map_tau]

theorem det_twist_ne (hp : p.det ≠ 0) {x : Fin j → Fin j → ℂ} (hx : (Matrix.of x).det ≠ 0) :
    (Matrix.of (twist p τ x)).det ≠ 0 := by
  rw [det_twist hp]
  exact (map_ne_zero τ).2 hx

theorem twist_mul (hp : p.det ≠ 0) (x y : Fin j → Fin j → ℂ) :
    Matrix.of (twist p τ fun r s => (Matrix.of x * Matrix.of y) r s) =
      Matrix.of (twist p τ x) * Matrix.of (twist p τ y) := by
  have e : (Matrix.of fun r s => (Matrix.of x * Matrix.of y) r s) = Matrix.of x * Matrix.of y := rfl
  rw [of_twist, of_twist, of_twist, e, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ (Ne.isUnit hp)]

theorem twist_inj (hp : p.det ≠ 0) {x y : Fin j → Fin j → ℂ}
    (h : Matrix.of (twist p τ x) = Matrix.of (twist p τ y)) : x = y := by
  have h2 := congrArg (fun M => p⁻¹ * (M * p)) h
  simp only [of_twist, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hp), Matrix.mul_one,
    Matrix.nonsing_inv_mul_cancel_left _ _ (Ne.isUnit hp)] at h2
  funext r s
  exact τ.injective (congrFun (congrFun h2 r) s)

theorem twist_surj (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) (hp : p.det ≠ 0) (y : Matrix (Fin j) (Fin j) ℂ) :
    ∃ x, Matrix.of (twist p τ x) = y := by
  refine ⟨fun r s => τ ((p⁻¹ * y * p) r s), ?_⟩
  have e : (Matrix.of fun r s => τ ((p⁻¹ * y * p) r s)).map τ = p⁻¹ * y * p := by
    ext r s
    simp only [Matrix.map_apply, Matrix.of_apply, tau_tau hτ]
  rw [of_twist, e]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hp), Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ (Ne.isUnit hp)]

theorem measurePreserving_twist (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) (hp : p.det ≠ 0) :
    MeasurePreserving (twist p τ) (haarLoc j) (haarLoc j) := by
  have hq : p⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det p (Ne.isUnit hp)).ne_zero
  have h1 := GlobalTheory.HaarMul.measurePreserving_mul_mul j p p⁻¹ hp hq
  rcases hτ with rfl | rfl
  · exact h1
  · exact h1.comp (haarLoc_conj_and_null j).1

theorem uMat_injective {n : ℕ} {ε : Fin n → Bool} {g h : Formalism.REAL.UJ ε} (e : uMat g = uMat h) : g = h :=
  Subtype.ext (Units.ext e)

theorem exists_leviChart : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (C : ∀ i, Matrix (Fin (j i)) (Fin n) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (τ τ₀ : ℂ →+* ℂ), (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) → (τ₀ = RingHom.id ℂ ∨ τ₀ = starRingEnd ℂ) → n = n₀ + 2 * ∑ i, j i → (∀ i, C i * A i = 1) → (∀ i k, i ≠ k → C i * A k = 0) → (∀ i k, (A i)ᴴ * Formalism.REAL.Jm ε * A k = 0) → (∀ i, (A i)ᴴ * Formalism.REAL.Jm ε * A₀ = 0) → A₀ᴴ * Formalism.REAL.Jm ε * A₀ = Formalism.REAL.Jm ε₀ → SpansFlag A W → IsIsoFlag ε j W → ∃ θ, IsLeviChart ε ε₀ W A A₀ τ τ₀ θ := by
  intro n n₀ a j ε ε₀ W A C A₀ τ τ₀ hτ hτ₀ hn hC1 hC0 hAA hA0 h00 hsp hiso
  obtain ⟨B, p, q, hB1, hB0, htri, hAB, hBA, hpq⟩ := BlockGS.block_gramSchmidt n a j A C hC1 hC0
  have hspB : SpansFlag B W := GlobalTheory.T.columnBlocksSpanFlag_of_block_triangular n a j A B p q W htri hAB hBA hsp
  have hBJA : ∀ (m : ℕ) (X : Matrix (Fin n) (Fin m) ℂ), (∀ i, (A i)ᴴ * Formalism.REAL.Jm ε * X = 0) →
      ∀ i, (B i)ᴴ * Formalism.REAL.Jm ε * X = 0 := by
    intro m X hX i
    rw [hBA i, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.sum_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc (q k i)ᴴ, Matrix.mul_assoc (q k i)ᴴ, hX, Matrix.mul_zero]
  have hBJB : ∀ i k, (B i)ᴴ * Formalism.REAL.Jm ε * B k = 0 := by
    intro i k
    refine hBJA _ _ (fun l => ?_) i
    rw [hBA k, Matrix.mul_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [← Matrix.mul_assoc, hAA, Matrix.zero_mul]
  obtain ⟨B₀, s, d, hF, hA₀⟩ := GlobalTheory.T.exists_orthonormalFrame_of_isotropicBlocks n n₀ a j ε ε₀ B A₀ hn hB1 hB0 hBJB (hBJA _ _ hA0) h00
  obtain ⟨θ₀, hθm, hθ⟩ := GlobalTheory.T.exists_measurable_unitaryLeviBlockMap n n₀ a j ε ε₀ B B₀ hF
  obtain ⟨C₀, hC₀, hC₀m⟩ := exists_conj_gauge_invariant n₀ ε₀ τ₀ hτ₀
  have hp : ∀ i, (p i i).det ≠ 0 := fun i => (Matrix.isUnit_det_of_right_inverse (hpq i)).ne_zero
  let R : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ :=
    Prod.map (fun x i => twist (p i i) τ (x i)) (fun g => s * C₀ g * s⁻¹)
  have hcont : Continuous fun g : Formalism.REAL.UJ ε₀ => s * C₀ g * s⁻¹ :=
    (continuous_const.mul C₀.continuous_toFun).mul continuous_const
  have hR1 : Measurable fun (x : ∀ i, Fin (j i) → Fin (j i) → ℂ) i => twist (p i i) τ (x i) :=
    measurable_pi_lambda _ fun i =>
      (measurePreserving_twist hτ (hp i)).measurable.comp (measurable_pi_apply i)
  have hRm : Measurable R := hR1.prodMap hcont.measurable
  have hθR : ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ₀ (R z)) =
      lev ε B B₀ (fun i => Matrix.of (twist (p i i) τ (z.1 i))) (uMat (s * C₀ z.2 * s⁻¹)) :=
    fun z hz => hθ (R z) fun i => det_twist_ne (hp i) (hz i)
  refine ⟨θ₀ ∘ R, hθm.comp hRm, fun m => ?_, fun z z' hz hz' => ⟨?_, fun e => ?_⟩,
    fun z hz => ⟨fun i => ?_, fun g hg hg0 => ?_⟩, fun μ c hμ hc => ?_⟩
  · rw [GlobalTheory.T.mem_isotropicFlagSelfAdjointLevi_iff_block n n₀ a j ε ε₀ B B₀ hF W hspB m]
    constructor
    · rintro ⟨x, g, hx, hm⟩
      choose y hy using fun i => twist_surj hτ (hp i) (x i)
      have hy0 : ∀ i, (Matrix.of (y i)).det ≠ 0 := by
        intro i h0
        apply hx i
        rw [← hy i, det_twist (hp i), h0, map_zero]
      refine ⟨(y, C₀.symm (s⁻¹ * g * s)), hy0, uMat_injective ?_⟩
      have e : s * C₀ (C₀.symm (s⁻¹ * g * s)) * s⁻¹ = g := by
        rw [ContinuousMulEquiv.apply_symm_apply]; group
      rw [Function.comp_apply, hθR _ hy0, hm]
      simp only [hy, e]
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, _, fun i => det_twist_ne (hp i) (hz i), hθR z hz⟩
  · apply uMat_injective
    have hzz : ∀ i, (Matrix.of fun r s => (Matrix.of (z.1 i) * Matrix.of (z'.1 i)) r s).det ≠ 0 := by
      intro i
      change (Matrix.of (z.1 i) * Matrix.of (z'.1 i)).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero (hz i) (hz' i)
    have e : uMat (s * C₀ (z.2 * z'.2) * s⁻¹) = uMat (s * C₀ z.2 * s⁻¹) * uMat (s * C₀ z'.2 * s⁻¹) := by
      change _ = uMat ((s * C₀ z.2 * s⁻¹) * (s * C₀ z'.2 * s⁻¹))
      congr 1
      rw [map_mul]; group
    change uMat (θ₀ (R z)) * uMat (θ₀ (R z')) = uMat (θ₀ (R _))
    rw [hθR z hz, hθR z' hz', hθR _ hzz, ← hF.lev_mul]
    simp only [twist_mul (hp _), e]
  · have e2 : uMat (θ₀ (R z)) = uMat (θ₀ (R z')) := congrArg uMat e
    rw [hθR z hz, hθR z' hz'] at e2
    obtain ⟨e3, e4⟩ := hF.lev_inj _ _ _ _ e2
    refine Prod.ext (funext fun i => twist_inj (τ := τ) (hp i) (congrFun e3 i)) ?_
    have e5 := uMat_injective e4
    exact C₀.injective (mul_left_cancel (mul_right_cancel e5))
  · rw [Function.comp_apply, Size.locSize_blocks n a j B W hB1 hB0 hspB _
      (fun i => Matrix.of (twist (p i i) τ (z.1 i))) (fun i => det_twist_ne (hp i) (hz i))
      (fun i => by rw [hθR z hz, hF.lev_mul_B]) i, det_twist (hp i), norm_tau hτ]
  · refine GlobalTheory.T.flagStabilizer_mul_inv_leviComponent_mem_unipotent n n₀ a j ε ε₀ B B₀ hF W A A₀ p d s (C₀ z.2) (fun i => (Matrix.of (z.1 i)).map τ) g _
      hsp hspB (fun k i h => (htri k i h).1) hp hAB hA₀ (fun i => ?_) hg (by rw [hC₀]; exact hg0) (hθR z hz)
    rw [det_map_tau]
    exact (map_ne_zero τ).2 (hz i)
  · have hR : MeasurePreserving R
        ((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod
          (ENNReal.ofReal c • Formalism.REAL.muG ε₀))
        ((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod
          (ENNReal.ofReal c • Formalism.REAL.muG ε₀)) := by
      refine MeasurePreserving.prod ?_ ⟨hcont.measurable, hC₀m s c hc⟩
      exact measurePreserving_pi _ _ fun i => (measurePreserving_twist hτ (hp i)).smul_measure _
    rw [← Measure.map_map hθm hRm, hR.map_eq]
    obtain ⟨g1, g2⟩ := GlobalTheory.T.levi_chart_map_haar_carried_invariant n n₀ a j ε ε₀ B B₀ hF W hspB θ₀ hθm hθ c
    have g3 := GlobalTheory.T.isRadial_map_unitaryLeviBlockProduct n n₀ a j ε ε₀ B B₀ hF θ₀ hθm hθ c hc
    have hν : IsGaugeSub (flagM ε W) (n₀ ^ 2 + 2 * ∑ i, j i ^ 2) _ := ⟨g1, g2, g3⟩
    have hd : n - 2 * ∑ i, j i = n₀ := by omega
    have halg := GlobalTheory.LeviAlgebra.exists_levi_algebra n ε a j W hiso
    rw [hd] at halg
    obtain ⟨𝒜, E, a1, a2, a3, a4⟩ := halg
    rw [a4] at hμ hν
    exact (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε 𝒜 _ E a1 a2 a3 _ hν).2.2.1 μ hμ

end GlobalTheory.LeviIso.Chart
