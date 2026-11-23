import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalShStatement
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.InfFam

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.Unf.MajInt

variable {D : D7}

def incInf (D : D7) : Ainf D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inl D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

theorem finPart_incInf (y : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    finPart D (incInf D y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e =>
    show (0 : Af D.host.F) ⊗ₜ[D.host.F] e = 0
    exact TensorProduct.zero_tmul _ _
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

theorem infPart_incInf (y : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    infPart D (incInf D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def realPt (D : D7) (w : D.what₂.Tau → ℂ) : AE D :=
  incInf D (Formalism.IndefR.Eqv.splitInv D w)

theorem theta_realPt {θ : InfFam D} (hθ : IsInfFam θ) (w : D.what₂.Tau → ℂ) (τ : D.what₂.Tau) :
    θ τ (infPart D (realPt D w)) = w τ := by
  rw [realPt, infPart_incInf, Formalism.IndefR.Eqv.eq_thetaC D hθ, Formalism.IndefR.Eqv.thetaC_splitInv]

open Classical in

def shift {m n : ℕ} (P : Fin m → Fin n → Prop) (z : D.what₂.Tau × Fin m × Fin n → ℤ × ℤ) : Mx D m n :=
  Matrix.of fun i j => if P i j then
    realPt D (fun τ => ((z (τ, i, j)).1 : ℂ) + ((z (τ, i, j)).2 : ℂ) * Complex.I) else 0

open Classical in
theorem compAt_shift {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (P : Fin m → Fin n → Prop)
    (z : D.what₂.Tau × Fin m × Fin n → ℤ × ℤ) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    compAt θ τ (shift P z) i j =
      if P i j then ((z (τ, i, j)).1 : ℂ) + ((z (τ, i, j)).2 : ℂ) * Complex.I else 0 := by
  classical
  simp only [compAt, Matrix.map_apply, shift, Matrix.of_apply]
  split_ifs
  · exact theta_realPt hθ _ τ
  · simp

theorem finPart_shift {m n : ℕ} (P : Fin m → Fin n → Prop) (z : D.what₂.Tau × Fin m × Fin n → ℤ × ℤ) (i : Fin m)
    (j : Fin n) : finPart D ((shift P z : Mx D m n) i j) = 0 := by
  classical
  simp only [shift, Matrix.of_apply]
  split_ifs
  · exact finPart_incInf _
  · simp

theorem shift_off {m n : ℕ} (P : Fin m → Fin n → Prop) (z : D.what₂.Tau × Fin m × Fin n → ℤ × ℤ) (i : Fin m)
    (j : Fin n) (h : ¬ P i j) : (shift P z : Mx D m n) i j = 0 := by
  classical
  simp [shift, h]

theorem norm_compAt_le (θ : InfFam D) {m n : ℕ} (x : Mx D m n) (τ : D.what₂.Tau) (i : Fin m) (j : Fin n) :
    ‖compAt θ τ x i j‖ ≤ realSize θ x := by
  unfold realSize
  calc ‖compAt θ τ x i j‖ ≤ ∑ j', ‖compAt θ τ x i j'‖ :=
        Finset.single_le_sum (f := fun j' => ‖compAt θ τ x i j'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖compAt θ τ x i' j'‖ :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖compAt θ τ x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ _ := Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', ‖compAt θ τ' x i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ τ)

end GlobalTheory.Unf.MajInt

namespace GlobalTheory.Unf.MajInt

theorem real_ineq (d R : ℕ) :
    (((1 + (R : ℝ)) ^ (2 * d + 2))⁻¹) * ((((2 * (R + 1) + 1) ^ 2) ^ d : ℕ) : ℝ) ≤ 9 ^ d * ((((R : ℝ) + 1) ^ 2)⁻¹) := by
  set s : ℝ := (R : ℝ) + 1 with hs
  have hs1 : 1 ≤ s := by rw [hs]; have : (0 : ℝ) ≤ R := Nat.cast_nonneg R; linarith
  have hs0 : 0 < s := by linarith
  have e1 : (1 + (R : ℝ)) = s := by rw [hs]; ring
  rw [e1]
  push_cast
  rw [← hs]
  have h1 : ((2 * s + 1) ^ 2) ^ d ≤ 9 ^ d * s ^ (2 * d) := by
    calc ((2 * s + 1) ^ 2) ^ d ≤ ((3 * s) ^ 2) ^ d :=
          pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 2) d
      _ = 9 ^ d * s ^ (2 * d) := by rw [pow_mul, ← mul_pow]; ring
  rw [inv_mul_le_iff₀ (by positivity)]
  have e2 : s ^ (2 * d + 2) * (9 ^ d * (s ^ 2)⁻¹) = 9 ^ d * s ^ (2 * d) := by
    rw [pow_add]; field_simp
  rw [e2]; exact h1

theorem summable_nine_pow_mul_inv_sq_succ (d : ℕ) : Summable fun R : ℕ => (9 : ℝ) ^ d * ((((R : ℝ) + 1) ^ 2)⁻¹) := by
  refine Summable.mul_left _ ?_
  have := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
  simpa using this

end GlobalTheory.Unf.MajInt

namespace GlobalTheory.Unf.MajInt

theorem maj_integrable : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (P : Fin m → Fin n → Prop)
    (a : Mx D m n) (μ : Measure (Mx D m n)), IsFiniteMeasureOnCompacts μ →
    (∀ᵐ x ∂μ, ∀ i j, ¬ P i j → x i j = a i j) →
    (∀ t : Mx D m n, (∀ i j, ¬ P i j → t i j = 0) → Measure.map (fun x => x + t) μ = μ) →
    ∃ N : ℕ, ∀ K : Set (Mx D m n), IsCompact K → Integrable (maj θ K N) μ := by
  intro D θ hθ m n P a μ hμ hae hinv
  classical
  set d := Fintype.card D.what₂.Tau * (m * n) with hd
  refine ⟨2 * d + 2, fun K hK => ?_⟩
  obtain ⟨hcl, hcont, hmeas, hcpt⟩ := (GlobalTheory.T.adelicMatrixSchwartzMajorant_measurable_rationalShift D θ hθ).1 m n K hK
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  set M : ℝ := realSize θ a + 2 * d with hM
  set Q := {x : Mx D m n | InBox K x ∧ realSize θ x ≤ M} with hQdef
  have hQ : μ Q < (⊤ : ℝ≥0∞) := (hcpt M).measure_lt_top
  let box : ℕ → Finset (D.what₂.Tau × Fin m × Fin n → ℤ × ℤ) := fun L =>
    Fintype.piFinset fun _ => Finset.Icc (-(L : ℤ)) L ×ˢ Finset.Icc (-(L : ℤ)) L
  have hcard : ∀ L : ℕ, (box L).card = ((2 * L + 1) ^ 2) ^ d := by
    intro L
    simp only [box, Fintype.card_piFinset, Finset.card_product, Int.card_Icc, Finset.prod_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, hd]
    have : (↑L + 1 - -(L : ℤ)).toNat = 2 * L + 1 := by omega
    rw [this, sq]
  have htr : ∀ z, μ ((fun x => x - shift P z) ⁻¹' Q) ≤ μ Q := by
    intro z
    have hoff : ∀ i j, ¬ P i j → (-shift (D := D) P z) i j = 0 := by
      intro i j h; rw [Matrix.neg_apply, shift_off P z i j h, neg_zero]
    have hm : Measurable (fun x : Mx D m n => x + -shift P z) := (continuous_add_right _).measurable
    calc μ ((fun x => x - shift P z) ⁻¹' Q) = μ ((fun x => x + -shift P z) ⁻¹' Q) := by
          simp only [sub_eq_add_neg]
      _ ≤ μ.map (fun x => x + -shift P z) Q := Measure.le_map_apply hm.aemeasurable Q
      _ = μ Q := by rw [hinv _ hoff]
  have hcov : ∀ L : ℕ, ∀ x : Mx D m n, (∀ i j, ¬ P i j → x i j = a i j) → InBox K x → realSize θ x ≤ L →
      ∃ z ∈ box L, x - shift P z ∈ Q := by
    intro L x hx hb hL
    let z : D.what₂.Tau × Fin m × Fin n → ℤ × ℤ := fun p =>
      (⌊(compAt θ p.1 x p.2.1 p.2.2).re⌋, ⌊(compAt θ p.1 x p.2.1 p.2.2).im⌋)
    have key : ∀ r : ℝ, |r| ≤ L → -(L : ℤ) ≤ ⌊r⌋ ∧ ⌊r⌋ ≤ L := by
      intro r hr
      rw [abs_le] at hr
      constructor
      · apply Int.le_floor.2; push_cast; linarith
      · have := Int.floor_le r
        exact_mod_cast (show (⌊r⌋ : ℝ) ≤ L by linarith)
    refine ⟨z, ?_, ?_, ?_⟩
    · simp only [box, Fintype.mem_piFinset, Finset.mem_product, Finset.mem_Icc]
      intro p
      have h1 := norm_compAt_le θ x p.1 p.2.1 p.2.2
      have hre := Complex.abs_re_le_norm (compAt θ p.1 x p.2.1 p.2.2)
      have him := Complex.abs_im_le_norm (compAt θ p.1 x p.2.1 p.2.2)
      exact ⟨key _ (by linarith), key _ (by linarith)⟩
    · obtain ⟨k, hk, hk0⟩ := hb
      refine ⟨k, hk, ?_⟩
      ext i j
      have h1 := congrFun (congrFun hk0 i) j
      have h2 := finPart_shift (D := D) P z i j
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.zero_apply, map_sub] at h1 ⊢
      rw [h2]; linear_combination h1
    · show realSize θ (x - shift P z) ≤ M
      have hterm : ∀ τ i j, ‖compAt θ τ (x - shift P z) i j‖ ≤ ‖compAt θ τ a i j‖ + 2 := by
        intro τ i j
        have e : compAt θ τ (x - shift P z) i j = compAt θ τ x i j - compAt θ τ (shift P z) i j := by
          simp only [compAt, Matrix.map_apply, Matrix.sub_apply, map_sub]
        rw [e, compAt_shift hθ]
        by_cases hP : P i j
        · rw [if_pos hP]
          refine le_trans ?_ (le_add_of_nonneg_left (norm_nonneg _))
          refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
          set c := compAt θ τ x i j
          have hre : (c - ((⌊c.re⌋ : ℤ) + (⌊c.im⌋ : ℤ) * Complex.I)).re = c.re - ⌊c.re⌋ := by simp
          have him : (c - ((⌊c.re⌋ : ℤ) + (⌊c.im⌋ : ℤ) * Complex.I)).im = c.im - ⌊c.im⌋ := by simp
          show |(c - ((⌊c.re⌋ : ℤ) + (⌊c.im⌋ : ℤ) * Complex.I)).re| +
            |(c - ((⌊c.re⌋ : ℤ) + (⌊c.im⌋ : ℤ) * Complex.I)).im| ≤ 2
          rw [hre, him]
          have a1 := Int.floor_le c.re
          have a2 := Int.lt_floor_add_one c.re
          have a3 := Int.floor_le c.im
          have a4 := Int.lt_floor_add_one c.im
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ c.re - ⌊c.re⌋),
            abs_of_nonneg (by linarith : (0 : ℝ) ≤ c.im - ⌊c.im⌋)]
          linarith
        · rw [if_neg hP, sub_zero]
          have : compAt θ τ x i j = compAt θ τ a i j := by
            simp only [compAt, Matrix.map_apply, hx i j hP]
          rw [this]; linarith
      unfold realSize
      calc ∑ τ, ∑ i, ∑ j, ‖compAt θ τ (x - shift P z) i j‖ ≤ ∑ τ, ∑ i, ∑ j, (‖compAt θ τ a i j‖ + 2) :=
            Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm τ i j
        _ = M := by
            simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              hM, hd, realSize]
            push_cast; ring
  have hS : ∀ L : ℕ, μ {x | InBox K x ∧ realSize θ x ≤ L} ≤ (box L).card * μ Q := by
    intro L
    calc μ {x | InBox K x ∧ realSize θ x ≤ L} ≤ μ (⋃ z ∈ box L, (fun x => x - shift P z) ⁻¹' Q) := by
          refine measure_mono_ae ?_
          filter_upwards [hae] with x hx
          intro hxS
          obtain ⟨z, hz, hq⟩ := hcov L x hx hxS.1 hxS.2
          exact Set.mem_biUnion hz hq
      _ ≤ ∑ z ∈ box L, μ ((fun x => x - shift P z) ⁻¹' Q) := measure_biUnion_finset_le _ _
      _ ≤ ∑ z ∈ box L, μ Q := Finset.sum_le_sum fun z _ => htr z
      _ = (box L).card * μ Q := by rw [Finset.sum_const, nsmul_eq_mul]
  have hSm : ∀ R : ℕ, MeasurableSet {x : Mx D m n | InBox K x ∧ realSize θ x ≤ ((R + 1 : ℕ) : ℝ)} := fun R =>
    (hcl.inter (isClosed_le hcont continuous_const)).measurableSet
  have hmaj : ∀ x, ENNReal.ofReal (maj θ K (2 * d + 2) x) ≤ ∑' R : ℕ,
      {x : Mx D m n | InBox K x ∧ realSize θ x ≤ ((R + 1 : ℕ) : ℝ)}.indicator
        (fun _ => ENNReal.ofReal (((1 + (R : ℝ)) ^ (2 * d + 2))⁻¹)) x := by
    intro x
    by_cases hb : InBox K x
    · have hx0 := realSize_nonneg θ x
      refine le_trans ?_ (ENNReal.le_tsum ⌊realSize θ x⌋₊)
      have hmem : InBox K x ∧ realSize θ x ≤ ((⌊realSize θ x⌋₊ + 1 : ℕ) : ℝ) :=
        ⟨hb, by push_cast; exact (Nat.lt_floor_add_one _).le⟩
      simp only [Set.indicator, Set.mem_setOf_eq]
      rw [if_pos hmem]
      unfold maj; rw [if_pos hb]
      apply ENNReal.ofReal_le_ofReal
      apply inv_anti₀ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      linarith [Nat.floor_le hx0]
    · unfold maj; rw [if_neg hb, ENNReal.ofReal_zero]; exact bot_le
  refine ⟨(hmeas _).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have henorm : ∀ x, ‖maj θ K (2 * d + 2) x‖ₑ = ENNReal.ofReal (maj θ K (2 * d + 2) x) := fun x => by
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (maj_nonneg _ _ _ _)]
  simp_rw [henorm]
  calc ∫⁻ x, ENNReal.ofReal (maj θ K (2 * d + 2) x) ∂μ
      ≤ ∫⁻ x, ∑' R : ℕ, {x : Mx D m n | InBox K x ∧ realSize θ x ≤ ((R + 1 : ℕ) : ℝ)}.indicator
        (fun _ => ENNReal.ofReal (((1 + (R : ℝ)) ^ (2 * d + 2))⁻¹)) x ∂μ := lintegral_mono hmaj
    _ = ∑' R : ℕ, ENNReal.ofReal (((1 + (R : ℝ)) ^ (2 * d + 2))⁻¹) *
          μ {x : Mx D m n | InBox K x ∧ realSize θ x ≤ ((R + 1 : ℕ) : ℝ)} := by
        rw [lintegral_tsum (fun R => (measurable_const.indicator (hSm R)).aemeasurable)]
        congr 1; funext R; exact lintegral_indicator_const (hSm R) _
    _ ≤ ∑' R : ℕ, ENNReal.ofReal (9 ^ d * ((((R : ℝ) + 1) ^ 2)⁻¹)) * μ Q := by
        refine ENNReal.tsum_le_tsum fun R => ?_
        calc ENNReal.ofReal (((1 + (R : ℝ)) ^ (2 * d + 2))⁻¹) *
              μ {x : Mx D m n | InBox K x ∧ realSize θ x ≤ ((R + 1 : ℕ) : ℝ)}
            ≤ ENNReal.ofReal (((1 + (R : ℝ)) ^ (2 * d + 2))⁻¹) * ((box (R + 1)).card * μ Q) := by
              gcongr; exact hS (R + 1)
          _ = ENNReal.ofReal (((1 + (R : ℝ)) ^ (2 * d + 2))⁻¹ * ((((2 * (R + 1) + 1) ^ 2) ^ d : ℕ) : ℝ)) * μ Q := by
              rw [hcard, ← mul_assoc, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
          _ ≤ ENNReal.ofReal (9 ^ d * ((((R : ℝ) + 1) ^ 2)⁻¹)) * μ Q := by
              exact mul_le_mul' (ENNReal.ofReal_le_ofReal (real_ineq d R)) le_rfl
    _ = ENNReal.ofReal (∑' R : ℕ, 9 ^ d * ((((R : ℝ) + 1) ^ 2)⁻¹)) * μ Q := by
        rw [ENNReal.tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg (fun R => by positivity) (summable_nine_pow_mul_inv_sq_succ d)]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hQ

end GlobalTheory.Unf.MajInt
