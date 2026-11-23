import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsInvInvariantOfRight
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumNormEntriesLeSumSingularValuesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableCoshPowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralExpNegMulSumNormStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LamBallULeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpLogNearOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHermitianLogUnitaryBlockDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumNormSqExpHermSubOneLeBlockMatStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsometricChartBlockHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InvariantMeasureLowerBoundOfChartStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoshConstNumericalBoundStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.CartanInt

variable {p q : ℕ}

theorem continuous_matrixEntryNormSum_unitaryPQ_sub_one : Continuous fun g : UpqT p q => l1 (UpqT.mat g - 1) := by
  have := GlobalTheory.UpqTopology.continuous_mat (P := p) (Q := q)
  unfold l1
  fun_prop

theorem smul_mem_lieU {H : Mat p q} (h : Hᴴ = H) (hK : IsKC H) : Complex.I • H ∈ lieU p q := by
  show (Complex.I • H)ᴴ * Formalism.UG.Jpq p q + Formalism.UG.Jpq p q * (Complex.I • H) = 0
  rw [Matrix.conjTranspose_smul, h]
  ext a b
  have := hK a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, sameBlock] at this ⊢ <;>
    simp [this]

theorem exp_mem_Kc {H : Mat p q} (h : Hᴴ = H) (hK : IsKC H) :
    GlobalTheory.CompactDualExists.expU ⟨Complex.I • H, smul_mem_lieU h hK⟩ ∈ Kc p q := by
  set J : Mat p q := Formalism.UG.Jpq p q with hJ
  have hJJ : J * J = 1 := GlobalTheory.UpqTopology.jpq_sq
  have h1 : J * (Complex.I • H) * J = Complex.I • H := by
    ext a b
    have := hK a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [hJ, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, sameBlock] at this ⊢ <;>
      simp [this]
  have h2 := Matrix.exp_conj J (Complex.I • H) ⟨⟨J, J, hJJ, hJJ⟩, rfl⟩
  rw [Matrix.inv_eq_left_inv hJJ, h1] at h2
  show IsKC (NormedSpace.exp (Complex.I • H))
  intro a b hab
  have e := congrFun (congrFun h2 a) b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [hJ, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, sameBlock] at e hab
  · exact self_eq_neg.mp e
  · exact self_eq_neg.mp e

theorem sq_matrixEntryNormSum_le_card_sq_mul_sum_sq (A : Mat p q) : l1 A ^ 2 ≤ ((p + q : ℕ) : ℝ) ^ 2 * ∑ a, ∑ b, ‖A a b‖ ^ 2 := by
  have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Ix p q × Ix p q)))
    (f := fun ab => ‖A ab.1 ab.2‖)
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at this
  simpa [l1, sq] using this

theorem measure_ball_K : ∀ (p q : ℕ) (mK : Measure (UpqT p q)), IsProbabilityMeasure mK → mK (Kc p q)ᶜ = 0 → (∀ k ∈ Kc p q, Measure.map (fun x => k * x) mK = mK) → ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 20 → ENNReal.ofReal ((δ / (9 / 2)) ^ (p ^ 2 + q ^ 2)) ≤ mK {k | l1 (UpqT.mat k - 1) ≤ (((p + q : ℕ) : ℝ) ^ 2 / 4 + ((p ^ 2 + q ^ 2 : ℕ) : ℝ)) * δ} := by
  intro p q mK hprob hK0 hleft δ hδ hδ'
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  obtain ⟨Φ, hΦc, hΦ, hiso, hsurj⟩ := GlobalTheory.T.exists_isometric_chart_blockHermitian p q
  let θ : ((Fin p × Fin p) ⊕ (Fin q × Fin q) → ℝ) → UpqT p q := fun R =>
    GlobalTheory.CompactDualExists.expU ⟨Complex.I • Φ R, smul_mem_lieU (hΦ R).1 (hΦ R).2⟩
  have hθc : Continuous θ :=
    GlobalTheory.CompactDualExists.continuous_expU.comp ((hΦc.const_smul Complex.I).subtype_mk _)
  have key := GlobalTheory.T.ofReal_pow_le_measure_of_chart_cover (UpqT p q) _ mK (Kc p q)
    {k | l1 (UpqT.mat k - 1) ≤ (((p + q : ℕ) : ℝ) ^ 2 / 4 + ((p ^ 2 + q ^ 2 : ℕ) : ℝ)) * δ} θ (89 / 20) δ hθc
    (isClosed_le continuous_matrixEntryNormSum_unitaryPQ_sub_one continuous_const) hK0
    (fun R => hleft _ (exp_mem_Kc (hΦ R).1 (hΦ R).2)) hδ (by norm_num) (by
      intro x hx
      obtain ⟨H, hH, hHK, hHb, hxH⟩ := GlobalTheory.T.exists_hermitian_log_unitaryBlockDiagonal p q x hx
      obtain ⟨R₀, rfl, hR₀⟩ := hsurj H hH hHK hHb
      refine ⟨R₀, hR₀, fun R hR => ?_⟩
      have e : UpqT.mat ((θ R)⁻¹ * x) =
          NormedSpace.exp (-(Complex.I • Φ R)) * NormedSpace.exp (Complex.I • Φ R₀) := by
        rw [mat_mul, hxH]; rfl
      show l1 (UpqT.mat ((θ R)⁻¹ * x) - 1) ≤ _
      rw [e]
      have a1 := GlobalTheory.T.sum_norm_sq_exp_herm_sub_one_le_blockMat p q (Φ R₀) (Φ R) (hΦ R₀).1 (hΦ R).1
      rw [hiso] at a1
      have a2 : ∑ i, (R₀ i - R i) ^ 2 ≤ ((p ^ 2 + q ^ 2 : ℕ) : ℝ) * δ ^ 2 := by
        refine (Finset.sum_le_card_nsmul _ _ (δ ^ 2) fun i _ => ?_).trans (le_of_eq ?_)
        · rw [← sq_abs, abs_sub_comm]; exact pow_le_pow_left₀ (abs_nonneg _) (hR i) 2
        · simp [sq]
      have a3 := (sq_matrixEntryNormSum_le_card_sq_mul_sum_sq _).trans (mul_le_mul_of_nonneg_left (a1.trans a2) (by positivity))
      refine le_of_sq_le_sq (a3.trans ?_) (by positivity)
      rw [mul_pow, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      nlinarith [sq_nonneg (((p + q : ℕ) : ℝ) ^ 2 / 4 - ((p ^ 2 + q ^ 2 : ℕ) : ℝ))])
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) key
  have : Fintype.card ((Fin p × Fin p) ⊕ (Fin q × Fin q)) = p ^ 2 + q ^ 2 := by simp [sq]
  rw [this]
  gcongr
  linarith

theorem weightAbsEntrySum_nonneg (A : Mat p q) : 0 ≤ l1 A := by unfold l1; positivity

theorem l1_add_le (A B : Mat p q) : l1 (A + B) ≤ l1 A + l1 B := by
  simp only [l1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => norm_add_le _ _

theorem matrixEntryAbsSum_mul_le (A B : Mat p q) : l1 (A * B) ≤ l1 A * l1 B := by
  calc l1 (A * B) ≤ ∑ i, ∑ j, ∑ k, ‖A i k‖ * ‖B k j‖ := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.mul_apply]
        exact (norm_sum_le _ _).trans (le_of_eq (by simp))
    _ = ∑ i, ∑ k, ‖A i k‖ * ∑ j, ‖B k j‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]; simp only [Finset.mul_sum]
    _ ≤ ∑ i, ∑ k, ‖A i k‖ * l1 B := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun k => ∑ j, ‖B k j‖) (fun _ _ => by positivity) (Finset.mem_univ k)
    _ = l1 A * l1 B := by simp only [l1, Finset.sum_mul]

theorem matrixEntryNormSum_upperRightBlockElement_le {B : Fin p → Fin q → ℂ} {δ : ℝ} (h : ∀ i j, ‖B i j‖ ≤ δ) :
    l1 (pY B) ≤ 2 * ((p * q : ℕ) : ℝ) * δ := by
  have h1 : ∑ i, ∑ j, ‖B i j‖ ≤ ((p * q : ℕ) : ℝ) * δ := by
    refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h i j).trans (le_of_eq ?_)
    simp [mul_assoc]
  have h2 : l1 (pY B) = ∑ i, ∑ j, ‖B i j‖ + ∑ i, ∑ j, ‖B i j‖ := by
    simp [l1, pY, pOf, Fintype.sum_sum_type]
    exact Finset.sum_comm
  linarith

theorem volume_polydisc {δ : ℝ} (hδ : 0 < δ) :
    volume (Set.univ.pi fun _ : Fin p => Set.univ.pi fun _ : Fin q => Metric.closedBall (0 : ℂ) δ) =
      ENNReal.ofReal ((Real.pi * δ ^ 2) ^ (p * q)) := by
  rw [volume_pi_pi]
  simp only [volume_pi_pi, Complex.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, mul_comm q p, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le,
    ENNReal.ofReal_pow hδ.le, mul_comm]
  congr 2
  rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

theorem const_le (m mK : Measure (UpqT p q)) (hm : Formalism.IndefR.Lev.IsMinf m) (c : ℝ) (hc : 0 < c)
    (hprob : IsProbabilityMeasure mK) (hK0 : mK (Kc p q)ᶜ = 0)
    (hleft : ∀ k ∈ Kc p q, Measure.map (fun x => k * x) mK = mK)
    (hf : ∀ f : UpqT p q → ENNReal, Measurable f → ∫⁻ g, f g ∂m = ENNReal.ofReal c *
      ∫⁻ B : Fin p → Fin q → ℂ, (∫⁻ k, f (k * eP B) ∂mK) * ENNReal.ofReal (polJ (pY B))) :
    c ≤ (18 / 5 * max 1 (3 / 2 * ((p + q : ℕ) : ℝ) ^ 2) / ((p + q : ℕ) : ℝ)) ^ ((p + q) ^ 2) *
      (9 / 2) ^ (p ^ 2 + q ^ 2) / Real.pi ^ (p * q) := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  obtain ⟨-, lam, hlam, ht⟩ := hm
  obtain ⟨ρ, hρ, hexp, hlog⟩ := GlobalTheory.T.exists_radius_exp_sub_one_le_and_exists_log p q
  set a : ℝ := ((p + q : ℕ) : ℝ) with ha
  set w : ℝ := max 1 (3 / 2 * a ^ 2) with hw
  have hw1 : 1 ≤ w := le_max_left _ _
  have hw2 : 3 / 2 * a ^ 2 ≤ w := le_max_right _ _
  have hw0 : 0 < w := by linarith
  have hpos : ∀ x : ℝ, 0 < x → 0 < (x / a) ^ ((p + q) ^ 2) := by
    intro x hx
    rcases Nat.eq_zero_or_pos (p + q) with h | h
    · rw [h]; simp
    · have : 0 < a := by rw [ha]; exact_mod_cast h
      positivity
  set Q : ℝ := (18 / 5 * w / a) ^ ((p + q) ^ 2) * (9 / 2) ^ (p ^ 2 + q ^ 2) / Real.pi ^ (p * q) with hQ
  have hQ0 : 0 < Q := by
    have := hpos (18 / 5 * w) (by positivity)
    have := Real.pi_pos
    positivity
  have hN : a ^ 2 = ((p ^ 2 + q ^ 2 : ℕ) : ℝ) + 2 * ((p * q : ℕ) : ℝ) := by rw [ha]; push_cast; ring
  have hd0 : (0 : ℝ) ≤ ((p ^ 2 + q ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have he0 : (0 : ℝ) ≤ ((p * q : ℕ) : ℝ) := Nat.cast_nonneg _
  have main : ENNReal.ofReal (c / Q) ≤ Formalism.L2.Theta.minfDensity (p + q) := by
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (lt_min hρ (show (0 : ℝ) < 1 / 20 by norm_num))] with r hr
    obtain ⟨hr0, hr⟩ := hr
    rw [lt_min_iff] at hr
    set δ := r / w with hδ
    have hδ0 : 0 < δ := div_pos hr0 hw0
    have hr' : r = w * δ := by rw [hδ]; field_simp
    have hδr : δ ≤ r := div_le_self hr0.le hw1
    have hNδ : 3 / 2 * a ^ 2 * δ ≤ r := by rw [hr']; gcongr
    set E := {g : UpqT p q | ∃ X ∈ ballU p q r, UpqT.mat g = NormedSpace.exp (X : Mat p q)} with hE
    set U := {k : UpqT p q | l1 (UpqT.mat k - 1) ≤ (a ^ 2 / 4 + ((p ^ 2 + q ^ 2 : ℕ) : ℝ)) * δ} with hU
    set D := Set.univ.pi fun _ : Fin p => Set.univ.pi fun _ : Fin q => Metric.closedBall (0 : ℂ) δ with hD
    have hUm : MeasurableSet U := (isClosed_le continuous_matrixEntryNormSum_unitaryPQ_sub_one continuous_const).measurableSet
    have hDm : MeasurableSet D := MeasurableSet.univ_pi fun _ => MeasurableSet.univ_pi fun _ =>
      measurableSet_closedBall
    have hsub : ∀ k ∈ U, ∀ B ∈ D, k * eP B ∈ E := by
      intro k hk B hB
      have hu : l1 (UpqT.mat k - 1) ≤ _ := hk
      have hy := matrixEntryNormSum_upperRightBlockElement_le (B := B) (δ := δ) fun i j => by simpa using hB i trivial j trivial
      have hy2 : 2 * ((p * q : ℕ) : ℝ) * δ ≤ a ^ 2 * δ := by gcongr; linarith
      have hv := hexp (pY B) (by nlinarith [hr.1])
      have e : UpqT.mat (k * eP B) - 1 = (UpqT.mat k - 1) + (NormedSpace.exp (pY B) - 1) +
          (UpqT.mat k - 1) * (NormedSpace.exp (pY B) - 1) := by
        rw [mat_mul, mat_eP]; noncomm_ring
      have b1 := l1_add_le ((UpqT.mat k - 1) + (NormedSpace.exp (pY B) - 1))
        ((UpqT.mat k - 1) * (NormedSpace.exp (pY B) - 1))
      have b2 := l1_add_le (UpqT.mat k - 1) (NormedSpace.exp (pY B) - 1)
      have b3 := matrixEntryAbsSum_mul_le (UpqT.mat k - 1) (NormedSpace.exp (pY B) - 1)
      have b4 : l1 (UpqT.mat k - 1) * l1 (NormedSpace.exp (pY B) - 1) ≤ l1 (UpqT.mat k - 1) * (1 / 20) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hr.2]) (weightAbsEntrySum_nonneg _)
      have b5 : (a ^ 2 / 4 + ((p ^ 2 + q ^ 2 : ℕ) : ℝ)) * δ + 2 * ((p * q : ℕ) : ℝ) * δ = 5 / 4 * (a ^ 2 * δ) := by
        have : ((p ^ 2 + q ^ 2 : ℕ) : ℝ) = a ^ 2 - 2 * ((p * q : ℕ) : ℝ) := by linarith
        rw [this]; ring
      have b6 : l1 (UpqT.mat (k * eP B) - 1) ≤ 7 / 8 * r := by rw [e]; linarith
      obtain ⟨X, hX, hXl⟩ := hlog (k * eP B) (by linarith [hr.1])
      exact ⟨X, show l1 (X : Mat p q) < r by linarith, hX⟩
    have hmE : ENNReal.ofReal (c * ((δ / (9 / 2)) ^ (p ^ 2 + q ^ 2) * (Real.pi * δ ^ 2) ^ (p * q))) ≤ m E := by
      rw [← measure_toMeasurable E, ← lintegral_indicator_one (measurableSet_toMeasurable m E),
        hf _ (measurable_one.indicator (measurableSet_toMeasurable m E)), ENNReal.ofReal_mul hc.le,
        ENNReal.ofReal_mul (by positivity), ← volume_polydisc hδ0, ← lintegral_indicator_const hDm]
      refine mul_le_mul_right (lintegral_mono fun B => ?_) _
      by_cases hB : B ∈ D
      · rw [Set.indicator_of_mem hB]
        refine le_trans ?_ (le_mul_of_one_le_right' (ENNReal.one_le_ofReal.2 (one_le_polJ (Matrix.of B))))
        refine (measure_ball_K p q mK hprob hK0 hleft δ hδ0 (by linarith [hr.2])).trans ?_
        rw [← lintegral_indicator_one hUm]
        refine lintegral_mono fun k => ?_
        by_cases hk : k ∈ U
        · rw [Set.indicator_of_mem hk, Set.indicator_of_mem (subset_toMeasurable m E (hsub k hk B hB))]
          exact le_rfl
        · rw [Set.indicator_of_notMem hk]; exact zero_le
      · rw [Set.indicator_of_notMem hB]; exact zero_le
    refine le_trans (le_of_eq ?_) (ENNReal.div_le_div hmE (GlobalTheory.T.lam_ballU_le_ofReal_pow p q lam hlam r hr0))
    rw [← ENNReal.ofReal_div_of_pos (hpos _ (by positivity))]
    congr 1
    have e1 : (18 / 5 * r / a) ^ ((p + q) ^ 2) =
        (18 / 5 * w / a) ^ ((p + q) ^ 2) * (δ ^ (p ^ 2 + q ^ 2) * (δ ^ 2) ^ (p * q)) := by
      rw [← pow_mul, ← pow_add, show p ^ 2 + q ^ 2 + 2 * (p * q) = (p + q) ^ 2 by ring, ← mul_pow, hr']
      congr 1; ring
    have := hpos (18 / 5 * w) (by positivity)
    have := Real.pi_pos
    rw [e1, hQ, div_pow δ, mul_pow Real.pi]
    field_simp
  have h1 : Formalism.L2.Theta.minfDensity (p + q) ≤ 1 :=
    ENNReal.inv_le_one.2 (one_le_pow₀ (by norm_num))
  have h2 := ENNReal.ofReal_le_one.1 (main.trans h1)
  rwa [div_le_one hQ0] at h2

theorem integrand_le {c : ℝ} (hc : 2 * (((p + q : ℕ) : ℝ) - 1) < c) {k : UpqT p q} (hk : k ∈ Kc p q)
    (B : Fin p → Fin q → ℂ) : coshPow c (k * eP B) * polJ (pY B) ≤ (2 : ℝ) ^ (c * (min p q : ℕ)) *
      Real.exp (-((c - 2 * (((p + q : ℕ) : ℝ) - 1)) / ((((p + q : ℕ) : ℝ) + 1) / 2) * ∑ i, ∑ j, ‖B i j‖)) := by
  have h1 : coshPow c (k * eP B) ≤ (2 : ℝ) ^ (c * (min p q : ℕ)) *
      Real.exp (-(c * ∑ i ∈ Finset.range (min p q), singVal (Matrix.of B) i)) := by
    unfold coshPow
    rw [cartanB_mul_eP hk, Real.rpow_mul_natCast (by norm_num), Finset.mul_sum, ← Finset.sum_neg_distrib,
      Real.exp_sum, ← Finset.card_range (min p q), ← Finset.prod_const, Finset.card_range,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun i _ => (Real.rpow_pos_of_pos (Real.cosh_pos _) _).le) fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    have hc0 : 0 ≤ c := by
      have : (1 : ℝ) ≤ ((p + q : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ p + q)
      linarith
    set s := singVal (Matrix.of B) i
    have b1 : Real.exp s / 2 ≤ Real.cosh s := by
      rw [Real.cosh_eq]; linarith [Real.exp_pos (-s)]
    calc Real.cosh s ^ (-c) ≤ (Real.exp s / 2) ^ (-c) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) b1 (by linarith)
      _ = _ := by
          rw [Real.div_rpow (by positivity) (by norm_num), ← Real.exp_mul, Real.rpow_neg (by norm_num),
            div_inv_eq_mul, mul_comm]
          congr 2; ring
  have h2 := polJ_le_exp (Matrix.of B)
  have h3 := GlobalTheory.T.sum_norm_entries_le_sum_singularValues p q (Matrix.of B)
  refine (mul_le_mul h1 h2 (zero_le_one.trans (one_le_polJ _)) (by positivity)).trans ?_
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
  have hs : 0 < (((p + q : ℕ) : ℝ) + 1) / 2 := by positivity
  have h4 : (c - 2 * (((p + q : ℕ) : ℝ) - 1)) / ((((p + q : ℕ) : ℝ) + 1) / 2) * ∑ i, ∑ j, ‖B i j‖ ≤
      (c - 2 * (((p + q : ℕ) : ℝ) - 1)) * ∑ i ∈ Finset.range (min p q), singVal (Matrix.of B) i := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    rw [div_le_iff₀' hs]; exact h3
  linarith

theorem lintegral_coshPow_le (m mK : Measure (UpqT p q)) (C : ℝ) (hC : 0 < C)
    (hprob : IsProbabilityMeasure mK) (hK0 : mK (Kc p q)ᶜ = 0)
    (hf : ∀ f : UpqT p q → ENNReal, Measurable f → ∫⁻ g, f g ∂m = ENNReal.ofReal C *
      ∫⁻ B : Fin p → Fin q → ℂ, (∫⁻ k, f (k * eP B) ∂mK) * ENNReal.ofReal (polJ (pY B)))
    {c : ℝ} (hc : 2 * (((p + q : ℕ) : ℝ) - 1) < c) :
    ∫⁻ g, ENNReal.ofReal (coshPow c g) ∂m ≤ ENNReal.ofReal (C * ((2 : ℝ) ^ (c * (min p q : ℕ)) *
      (2 * Real.pi / ((c - 2 * (((p + q : ℕ) : ℝ) - 1)) / ((((p + q : ℕ) : ℝ) + 1) / 2)) ^ 2) ^ (p * q))) := by
  rw [hf _ (GlobalTheory.T.measurable_coshPow' p q c).ennreal_ofReal, ENNReal.ofReal_mul hC.le, ENNReal.ofReal_mul (by positivity),
    ← GlobalTheory.T.lintegral_exp_neg_mul_sum_norm_matrix p q _ (div_pos (by linarith) (by positivity)), ← lintegral_const_mul' (ENNReal.ofReal (2 ^ _)) _ ENNReal.ofReal_ne_top]
  refine mul_le_mul_right (lintegral_mono fun B => ?_) _
  rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, ← ENNReal.ofReal_mul (by positivity)]
  refine le_trans (lintegral_mono_ae ?_) (le_of_eq (by rw [lintegral_const, measure_univ, mul_one]))
  filter_upwards [show ∀ᵐ k ∂mK, k ∈ Kc p q from hK0] with k hk
  rw [← ENNReal.ofReal_mul (coshPow_pos _ _).le]
  exact ENNReal.ofReal_le_ofReal (integrand_le hc hk B)

theorem coshPow_anti {c c' : ℝ} (h : c ≤ c') (g : UpqT p q) : coshPow c' g ≤ coshPow c g :=
  Finset.prod_le_prod (fun _ _ => (Real.rpow_pos_of_pos (Real.cosh_pos _) _).le) fun _ _ =>
    Real.rpow_le_rpow_of_exponent_le (Real.one_le_cosh _) (neg_le_neg h)

theorem coshFinite : CoshFinite := by
  intro p q m hm c hc
  obtain ⟨C, mK, hC, hprob, hK0, -, hf⟩ := haar_polar p q m hm.1
  refine ⟨(GlobalTheory.T.measurable_coshPow' p q c).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun g => (coshPow_pos c g).le)]
  exact (lintegral_coshPow_le m mK C hC hprob hK0 hf hc).trans_lt ENNReal.ofReal_lt_top

theorem coshLocUnif : CoshLocUnif := by
  intro p q m hm c₀ hc
  refine ⟨(c₀ - 2 * (((p + q : ℕ) : ℝ) - 1)) / 2, by linarith,
    coshPow (c₀ - (c₀ - 2 * (((p + q : ℕ) : ℝ) - 1)) / 2), coshFinite p q m hm _ (by linarith),
    fun c h g => coshPow_anti ?_ g⟩
  linarith [(abs_lt.1 h).1]

theorem coshBound : CoshBound := by
  intro p q m hm n t hn
  have hn' : ((p + q : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : p + q ≤ n)
  have hi := coshFinite p q m hm (2 * n) (by linarith)
  have hc : 2 * (((p + q : ℕ) : ℝ) - 1) < 2 * ((p + q : ℕ) : ℝ) := by linarith
  have hi' := coshFinite p q m hm _ hc
  refine ⟨hi, (integral_mono hi hi' fun g => coshPow_anti (by linarith) g).trans ?_⟩
  obtain ⟨C, mK, hC, hprob, hK0, hleft, hf⟩ := haar_polar p q m hm.1
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun g => (coshPow_pos _ g).le) hi'.1]
  refine ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le
    ((lintegral_coshPow_le m mK C hC hprob hK0 hf hc).trans (ENNReal.ofReal_le_ofReal ?_))
  refine le_trans ?_ (GlobalTheory.T.cosh_constant_le_exp_three_mul_sq_mul_log p q)
  rw [show 2 * ((p + q : ℕ) : ℝ) - 2 * (((p + q : ℕ) : ℝ) - 1) = 2 by ring,
    show 2 * ((p + q : ℕ) : ℝ) * ((min p q : ℕ) : ℝ) = ((2 * (p + q) * min p q : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast]
  exact mul_le_mul_of_nonneg_right (const_le m mK hm C hC hprob hK0 hleft hf) (by positivity)

theorem coshIntegral : CoshIntegral := ⟨coshFinite, coshLocUnif, coshBound⟩

end GlobalTheory.CartanInt
