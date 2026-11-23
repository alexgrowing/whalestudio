import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.RightDerivativeZeroOutsideSupport
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.DecayHypothesisOfLargeConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace ContDiff Convolution

noncomputable section

namespace Formalism.MainNotions.BridgeCPX

open Formalism.MainNotions.S Formalism.REAL

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section PI

variable {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [hB : BorelSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]

theorem contDiff_param_integral {μ : Measure E} {f : E → V} (hf : LocallyIntegrable f μ) {Ψ : P → E → ℂ}
    {k : Set E} (hk : IsCompact k) (hΨ0 : ∀ p x, x ∉ k → Ψ p x = 0) (hΨ : ContDiff ℝ ∞ (Function.uncurry Ψ)) :
    ContDiff ℝ ∞ (fun p => ∫ y, Ψ p y • f y ∂μ) := by
  have hk' : IsCompact (-k) := hk.neg
  have key := contDiffOn_convolution_right_with_param_comp (𝕜 := ℝ) (μ := μ) (n := (⊤ : ℕ∞))
    ((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] V →L[ℝ] V).flip) (s := (Set.univ : Set P)) (v := fun _ => (0 : E))
    contDiffOn_const (f := f) (g := fun p x => Ψ p (-x)) (k := -k) isOpen_univ hk'
    (fun p x _ hx => hΨ0 p (-x) (by simpa using hx)) hf
    (by
      apply ContDiff.contDiffOn
      exact hΨ.comp (contDiff_fst.prodMk contDiff_snd.neg))
  rw [contDiffOn_univ] at key
  have e : (fun p => ∫ y, Ψ p y • f y ∂μ) =
      fun x => (f ⋆[(ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] V →L[ℝ] V).flip, μ] (fun x' => Ψ x (-x'))) 0 := by
    funext p
    simp [convolution]
  rw [e]
  exact key

end PI

section Vec

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsTest (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop := ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ

theorem continuous_umat : Continuous (fun y : UJ ε => umat y) := (isClosedEmbeddingMatrix n ε).1.continuous

theorem umat_mem (y : UJ ε) : umat y ∈ UJset ε := y.2

theorem cont_orbit {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H) :
    Continuous (fun y : UJ ε => σ (umat y) w) :=
  (hσ.2.2 w).comp_continuous continuous_umat umat_mem

theorem test_comp_cs {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) :
    HasCompactSupport (fun y : UJ ε => Φ (umat y)) :=
  hΦ.2.comp_isClosedEmbedding (isClosedEmbeddingMatrix n ε).1

def vec (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) : H :=
  ∫ y : UJ ε, Φ (umat y) • σ (umat y) w ∂(muG ε)

theorem vec_integrable {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H)
    {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) :
    Integrable (fun y : UJ ε => Φ (umat y) • σ (umat y) w) (muG ε) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hΦ.1.continuous.comp continuous_umat).smul (cont_orbit hσ w)
  · exact (test_comp_cs hΦ).smul_right

theorem test_integrable {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) :
    Integrable (fun y : UJ ε => Φ (umat y)) (muG ε) :=
  (hΦ.1.continuous.comp continuous_umat).integrable_of_hasCompactSupport (test_comp_cs hΦ)

theorem rep_mul {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (a b : UJ ε) (v : H) :
    σ (umat (a * b)) v = σ (umat a) (σ (umat b) v) := by
  have := hσ.1.2 (umat a) (umat_mem a) (umat b) (umat_mem b)
  show σ (umat a * umat b) v = _
  rw [this]; rfl

theorem rep_inv_apply {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (a : UJ ε) (v : H) :
    σ (umat a⁻¹) (σ (umat a) v) = v := by
  rw [← rep_mul hσ, inv_mul_cancel]
  show σ 1 v = v
  rw [hσ.1.1]; rfl

theorem rep_inner {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (a : UJ ε) (u v : H) :
    ⟪σ (umat a) u, σ (umat a) v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(σ (umat a) : H →ₗ[ℂ] H), fun x => hσ.2.1 _ (umat_mem a) x⟩
  exact L.inner_map_map u v

theorem rep_inner_left {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (a : UJ ε) (u v : H) :
    ⟪σ (umat a) u, v⟫_ℂ = ⟪u, σ (umat a⁻¹) v⟫_ℂ := by
  rw [← rep_inner hσ a⁻¹, rep_inv_apply hσ]

def ltr (a : Matrix (Fin n) (Fin n) ℂ) (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun m => Φ (a * m)

variable [CompleteSpace H]

theorem rep_vec {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H)
    {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) (g : UJ ε) :
    σ (umat g⁻¹) (vec ε σ w Φ) = vec ε σ w (ltr (umat g) Φ) := by
  unfold vec
  rw [← ContinuousLinearMap.integral_comp_comm _ (vec_integrable hσ w hΦ)]
  rw [← integral_mul_left_eq_self (fun y : UJ ε => ltr (umat g) Φ (umat y) • σ (umat y) w) g⁻¹]
  congr 1
  funext y
  rw [map_smul, ← rep_mul hσ]
  congr 2
  have : umat g * umat (g⁻¹ * y) = umat (g * (g⁻¹ * y)) := rfl
  rw [this, mul_inv_cancel_left]

end Vec

section Bound

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem hs_nonneg' (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs g := by unfold hs; positivity

theorem continuous_hs : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => hs g) := by
  unfold hs
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply_apply i j).norm).pow 2

theorem test_hs_bound {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ m, Φ m ≠ 0 → hs m ≤ R := by
  obtain ⟨R, hR⟩ := (hΦ.2.isCompact.image continuous_hs).bddAbove
  refine ⟨max R 1, le_max_right _ _, fun m hm => le_trans (hR ⟨m, subset_tsupport _ hm, rfl⟩) (le_max_left _ _)⟩

theorem hs_inv (a : UJ ε) : hs (umat a⁻¹) = hs (umat a) := by
  have h1 := (indefinite_unitary_inv_closed n ε (umat a) (umat_mem a)).2
  have h2 : umat a⁻¹ = Jm ε * (umat a)ᴴ * Jm ε := by
    have h3 : umat a⁻¹ * umat a = 1 := by
      show umat (a⁻¹ * a) = 1
      rw [inv_mul_cancel]; rfl
    have h4 := (indefinite_unitary_inv_closed n ε (umat a) (umat_mem a)).1
    calc umat a⁻¹ = umat a⁻¹ * (umat a * (Jm ε * (umat a)ᴴ * Jm ε)) := by rw [h4, Matrix.mul_one]
      _ = Jm ε * (umat a)ᴴ * Jm ε := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [h2]
  unfold hs Jm
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e1 : ∀ b : Bool, ‖(if b = true then (1 : ℂ) else -1)‖ = 1 := by intro b; split_ifs <;> simp
  rw [norm_mul, norm_mul, e1, e1, norm_star]
  ring

theorem hs_one : hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  unfold hs
  have : ∀ i j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs <;> simp
  simp [this]

theorem hs_zero_iff (a b : UJ ε) : hs (umat a) = 0 → hs (umat b) = 0 := by
  intro h
  have h1 : hs (umat a * umat a⁻¹) ≤ hs (umat a) * hs (umat a⁻¹) := frobenius_mul_le _ _
  have h2 : umat a * umat a⁻¹ = 1 := by
    show umat (a * a⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  rw [h2, hs_one, h, zero_mul] at h1
  have hn : n = 0 := by exact_mod_cast le_antisymm h1 (Nat.cast_nonneg n)
  subst hn
  simp [hs]

theorem inv_natPow_rpow_neg_half_even_eq_pow {A c x y : ℝ} (hA : 0 ≤ A) (hc : 1 ≤ c) (hx : 0 ≤ x) (h0 : x = 0 → y = 0) (hy0 : 0 ≤ y) (h0' : y = 0 → x = 0) (h : y ≤ c * x) :
    Real.sqrt x ^ (-A) ≤ Real.sqrt c ^ A * Real.sqrt y ^ (-A) := by
  rcases hx.eq_or_lt with hx0 | hx0
  · have hy : y = 0 := h0 hx0.symm
    rw [← hx0, hy]
    have h1 : 1 ≤ Real.sqrt c ^ A := Real.one_le_rpow (Real.one_le_sqrt.2 hc) hA
    have h2 : 0 ≤ Real.sqrt 0 ^ (-A) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    nlinarith
  · have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
    have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 (by linarith)
    rcases le_or_gt y 0 with hy | hy
    · rw [Real.sqrt_eq_zero_of_nonpos hy]
      rcases hA.eq_or_lt with hA0 | hA0
      · simp [← hA0]
      · exfalso
        have := h0' (le_antisymm hy hy0)
        linarith
    · have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
      have h3 : Real.sqrt y ≤ Real.sqrt c * Real.sqrt x := by
        rw [← Real.sqrt_mul (by linarith)]
        exact Real.sqrt_le_sqrt h
      have h4 : Real.sqrt y ^ A ≤ Real.sqrt c ^ A * Real.sqrt x ^ A := by
        rw [← Real.mul_rpow hsc.le hsx.le]
        exact Real.rpow_le_rpow hsy.le h3 hA
      rw [Real.rpow_neg hsx.le, Real.rpow_neg hsy.le]
      have p1 : 0 < Real.sqrt x ^ A := Real.rpow_pos_of_pos hsx _
      have p2 : 0 < Real.sqrt y ^ A := Real.rpow_pos_of_pos hsy _
      rw [← div_eq_mul_inv, le_div_iff₀ p2, inv_mul_le_iff₀ p1]
      linarith

theorem coef_bound {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H)
    {A C0 : ℝ} (hA : 0 ≤ A) (hC0 : 0 ≤ C0)
    (hdec : ∀ g : UJ ε, ‖⟪w, σ (umat g) w⟫_ℂ‖ ≤ C0 * Real.sqrt (hs (umat g)) ^ (-A))
    {Φ Φ' : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) (hΦ' : IsTest Φ') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : UJ ε, ‖⟪vec ε σ w Φ', σ (umat g) (vec ε σ w Φ)⟫_ℂ‖ ≤ C * Real.sqrt (hs (umat g)) ^ (-A) := by
  obtain ⟨R, hR1, hR⟩ := test_hs_bound hΦ
  obtain ⟨R', hR1', hR'⟩ := test_hs_bound hΦ'
  set I := ∫ y : UJ ε, ‖Φ (umat y)‖ ∂(muG ε) with hI
  set I' := ∫ y : UJ ε, ‖Φ' (umat y)‖ ∂(muG ε) with hI'
  have hI0 : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  have hI0' : 0 ≤ I' := integral_nonneg fun _ => norm_nonneg _
  set K := C0 * Real.sqrt (R * R') ^ A with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨I * (I' * K), by positivity, fun g => ?_⟩
  set N := Real.sqrt (hs (umat g)) ^ (-A) with hN
  have hN0 : 0 ≤ N := Real.rpow_nonneg (Real.sqrt_nonneg _) _

  have hpt : ∀ a b : UJ ε, Φ (umat a) ≠ 0 → Φ' (umat b) ≠ 0 →
      ‖⟪σ (umat b) w, σ (umat g) (σ (umat a) w)⟫_ℂ‖ ≤ K * N := by
    intro a b ha hb
    rw [rep_inner_left hσ, ← rep_mul hσ, ← rep_mul hσ]
    refine le_trans (hdec _) ?_
    have eK : K * N = C0 * (Real.sqrt (R * R') ^ A * N) := by rw [hK]; ring
    rw [eK]
    apply mul_le_mul_of_nonneg_left ?_ hC0

    have e1 : umat g = umat b * umat (b⁻¹ * g * a) * umat a⁻¹ := by
      show umat g = umat (b * (b⁻¹ * g * a) * a⁻¹)
      congr 2
      group
    have e2 : hs (umat g) ≤ (R * R') * hs (umat (b⁻¹ * g * a)) := by
      rw [e1]
      refine le_trans (frobenius_mul_le _ _) ?_
      rw [hs_inv]
      have := frobenius_mul_le (umat b) (umat (b⁻¹ * g * a))
      have h1 := hR _ ha
      have h2 := hR' _ hb
      have h0 := hs_nonneg' (umat (b⁻¹ * g * a))
      have h3 := hs_nonneg' (umat a)
      have h4 := hs_nonneg' (umat b)
      calc hs (umat b * umat (b⁻¹ * g * a)) * hs (umat a)
          ≤ (hs (umat b) * hs (umat (b⁻¹ * g * a))) * hs (umat a) := mul_le_mul_of_nonneg_right this h3
        _ ≤ (R' * hs (umat (b⁻¹ * g * a))) * R := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right h2 h0) h1 h3 (by positivity)
        _ = _ := by ring
    exact inv_natPow_rpow_neg_half_even_eq_pow hA (by nlinarith) (hs_nonneg' _) (hs_zero_iff _ _) (hs_nonneg' _) (hs_zero_iff _ _) e2

  have hin : ∀ u : H, (∀ b : UJ ε, Φ' (umat b) ≠ 0 → ‖⟪σ (umat b) w, u⟫_ℂ‖ ≤ K * N) →
      ‖⟪vec ε σ w Φ', u⟫_ℂ‖ ≤ I' * (K * N) := by
    intro u hu
    rw [← norm_inner_symm, vec, ← integral_inner (vec_integrable hσ w hΦ')]
    refine le_trans (norm_integral_le_integral_norm _) ?_
    rw [hI', ← integral_mul_const]
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
      ((test_integrable hΦ').norm.mul_const _)
    refine Eventually.of_forall fun b => ?_
    show ‖⟪u, Φ' (umat b) • σ (umat b) w⟫_ℂ‖ ≤ ‖Φ' (umat b)‖ * (K * N)
    rw [inner_smul_right, norm_mul]
    by_cases hb : Φ' (umat b) = 0
    · simp [hb]
    · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      rw [norm_inner_symm]
      exact hu b hb
  have e3 : ⟪vec ε σ w Φ', σ (umat g) (vec ε σ w Φ)⟫_ℂ =
      ∫ a : UJ ε, ⟪vec ε σ w Φ', σ (umat g) (Φ (umat a) • σ (umat a) w)⟫_ℂ ∂(muG ε) := by
    have := ContinuousLinearMap.integral_comp_comm ((innerSL ℂ (vec ε σ w Φ')).comp (σ (umat g)))
      (vec_integrable hσ w hΦ)
    exact this.symm
  rw [e3]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  rw [mul_assoc, hI, ← integral_mul_const]
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    ((test_integrable hΦ).norm.mul_const _)
  refine Eventually.of_forall fun a => ?_
  show ‖⟪vec ε σ w Φ', σ (umat g) (Φ (umat a) • σ (umat a) w)⟫_ℂ‖ ≤ ‖Φ (umat a)‖ * (I' * K * N)
  rw [map_smul, inner_smul_right, norm_mul]
  by_cases ha : Φ (umat a) = 0
  · simp [ha]
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [mul_assoc]
    exact hin _ fun b hb => hpt a b ha hb

end Bound

section Der

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def lmulL (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a)

def rmulL (a : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ a)

@[simp] theorem lmulL_apply (a m : Matrix (Fin n) (Fin n) ℂ) : lmulL a m = a * m := rfl
@[simp] theorem rmulL_apply (a m : Matrix (Fin n) (Fin n) ℂ) : rmulL a m = m * a := rfl

theorem test_ltr {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) (g : UJ ε) : IsTest (ltr (umat g) Φ) := by
  constructor
  · exact hΦ.1.comp (lmulL (umat g)).contDiff
  · let e : Matrix (Fin n) (Fin n) ℂ ≃ₜ Matrix (Fin n) (Fin n) ℂ :=
      { toFun := fun m => umat g * m
        invFun := fun m => umat g⁻¹ * m
        left_inv := fun m => by
          show umat g⁻¹ * (umat g * m) = m
          rw [← Matrix.mul_assoc]
          have : umat g⁻¹ * umat g = umat (g⁻¹ * g) := rfl
          rw [this, inv_mul_cancel]; exact Matrix.one_mul m
        right_inv := fun m => by
          show umat g * (umat g⁻¹ * m) = m
          rw [← Matrix.mul_assoc]
          have : umat g * umat g⁻¹ = umat (g * g⁻¹) := rfl
          rw [this, mul_inv_cancel]; exact Matrix.one_mul m
        continuous_toFun := (lmulL (umat g)).continuous
        continuous_invFun := (lmulL (umat g⁻¹)).continuous }
    exact hΦ.2.comp_homeomorph e

def der (Y : Matrix (Fin n) (Fin n) ℂ) (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun m => fderiv ℝ Φ m (Y * m)

theorem test_der {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) (Y : Matrix (Fin n) (Fin n) ℂ) :
    IsTest (der Y Φ) := by
  constructor
  · exact (hΦ.1.fderiv_right (m := ∞) (by simp)).clm_apply (lmulL Y).contDiff
  · apply (hΦ.2.fderiv (𝕜 := ℝ)).mono
    intro m hm
    simp only [Function.mem_support, der] at hm ⊢
    intro h0
    rw [h0] at hm
    exact hm rfl

theorem hasDerivAt_exp_mul (Y m : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • Y) * m) (Y * (NormedSpace.exp ((t : ℂ) • Y) * m)) t := by
  have h0 : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • Y)) Y 0 := by
    simpa using hasDerivAt_mul_exp_smul_zero 1 Y
  have h1 : HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • Y) * (NormedSpace.exp ((t : ℂ) • Y) * m))
      (Y * (NormedSpace.exp ((t : ℂ) • Y) * m)) 0 :=
    (rmulL (NormedSpace.exp ((t : ℂ) • Y) * m)).hasFDerivAt.comp_hasDerivAt 0 h0
  have h2 := HasDerivAt.comp_sub_const (f := fun s : ℝ => NormedSpace.exp ((s : ℂ) • Y) *
    (NormedSpace.exp ((t : ℂ) • Y) * m)) t t (by rw [sub_self]; exact h1)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  show NormedSpace.exp ((s : ℂ) • Y) * m = NormedSpace.exp (((s - t : ℝ) : ℂ) • Y) * (NormedSpace.exp ((t : ℂ) • Y) * m)
  rw [← Matrix.mul_assoc, ← one_parameter_subgroup_holds n Y (s - t) t, sub_add_cancel]

theorem hasDerivAt_test_curve {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) (Y m : Matrix (Fin n) (Fin n) ℂ)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => Φ (NormedSpace.exp ((s : ℂ) • Y) * m)) (der Y Φ (NormedSpace.exp ((t : ℂ) • Y) * m)) t :=
  ((hΦ.1.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_mul Y m t)

end Der

section DerVec

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem continuous_exp_smul (Y : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun s : ℝ => NormedSpace.exp ((s : ℂ) • Y)) := by
  have : ∀ t : ℝ, HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : ℂ) • Y)) (Y * (NormedSpace.exp ((t : ℂ) • Y) * 1)) t := by
    intro t
    simpa using hasDerivAt_exp_mul Y 1 t
  exact continuous_iff_continuousAt.2 fun t => (this t).continuousAt

theorem test_bounded {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) : ∃ B : ℝ, ∀ m, ‖Φ m‖ ≤ B :=
  hΦ.2.exists_bound_of_continuous hΦ.1.continuous

theorem exp_neg_mul_exp (Y : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (((-t : ℝ) : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y) = 1 := by
  rw [← one_parameter_subgroup_holds n Y (-t) t]
  simp

theorem umat_expG {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) (t : ℝ) :
    umat (expG ε Y t) = NormedSpace.exp ((t : ℂ) • Y) := toM_expG ε Y t hY

theorem test_ltr_exp {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) {Y : Matrix (Fin n) (Fin n) ℂ}
    (hY : inG ε Y) (t : ℝ) : IsTest (ltr (NormedSpace.exp ((t : ℂ) • Y)) Φ) := by
  rw [← umat_expG hY t]
  exact test_ltr hΦ _

variable [CompleteSpace H]

theorem hasDerivAt_vec {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H)
    {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inG ε Y) :
    HasDerivAt (fun t : ℝ => vec ε σ w (ltr (NormedSpace.exp ((t : ℂ) • Y)) Φ)) (vec ε σ w (der Y Φ)) 0 := by
  have hΘ := test_der hΦ Y
  obtain ⟨B, hB⟩ := test_bounded hΘ

  let 𝒦 : Set (Matrix (Fin n) (Fin n) ℂ) :=
    (fun p : ℝ × Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp (((-p.1 : ℝ) : ℂ) • Y) * p.2) ''
      (Set.Icc (-1 : ℝ) 1 ×ˢ tsupport (der Y Φ))
  have h𝒦 : IsCompact 𝒦 := by
    apply (isCompact_Icc.prod hΘ.2.isCompact).image
    have c1 : Continuous (fun p : ℝ × Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp (((-p.1 : ℝ) : ℂ) • Y)) :=
      (continuous_exp_smul Y).comp continuous_fst.neg
    exact c1.matrix_mul continuous_snd
  let S : Set (UJ ε) := (fun y : UJ ε => umat y) ⁻¹' 𝒦
  have hS : IsCompact S := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage h𝒦
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muG ε) (𝕜 := ℝ) (x₀ := (0 : ℝ))
    (s := Set.Ioo (-1 : ℝ) 1)
    (F := fun t y => ltr (NormedSpace.exp ((t : ℂ) • Y)) Φ (umat y) • σ (umat y) w)
    (F' := fun t y => der Y Φ (NormedSpace.exp ((t : ℂ) • Y) * umat y) • σ (umat y) w)
    (bound := S.indicator fun _ => B * ‖w‖)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (vec_integrable hσ w (test_ltr_exp hΦ hY t)).aestronglyMeasurable)
    (vec_integrable hσ w (test_ltr_exp hΦ hY 0))
    (by
      have := (vec_integrable hσ w (test_ltr_exp hΘ hY 0)).aestronglyMeasurable
      exact this)
    (Eventually.of_forall fun y t ht => by
      show ‖der Y Φ (NormedSpace.exp ((t : ℂ) • Y) * umat y) • σ (umat y) w‖ ≤ _
      rw [norm_smul, hσ.2.1 _ (umat_mem y)]
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy]
        exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hy]
        have : der Y Φ (NormedSpace.exp ((t : ℂ) • Y) * umat y) = 0 := by
          by_contra hne
          apply hy
          refine ⟨(t, NormedSpace.exp ((t : ℂ) • Y) * umat y), ⟨⟨ht.1.le, ht.2.le⟩, subset_tsupport _ hne⟩, ?_⟩
          show NormedSpace.exp (((-t : ℝ) : ℂ) • Y) * (NormedSpace.exp ((t : ℂ) • Y) * umat y) = umat y
          rw [← Matrix.mul_assoc, exp_neg_mul_exp, Matrix.one_mul]
        rw [this]; simp)
    ((integrable_indicator_iff hS.measurableSet).2 (integrableOn_const (hS.measure_lt_top.ne)))
    (Eventually.of_forall fun y t _ => by
      exact (hasDerivAt_test_curve hΦ Y (umat y) t).smul_const _)
  have e := key.2
  have e0 : (∫ y : UJ ε, der Y Φ (NormedSpace.exp (((0 : ℝ) : ℂ) • Y) * umat y) • σ (umat y) w ∂(muG ε)) =
      vec ε σ w (der Y Φ) := by
    simp [vec]
  rw [e0] at e
  exact e

end DerVec

section Cls

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inG_neg {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) : inG ε (-X) := by
  unfold inG at *
  rw [Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX, neg_zero]

theorem expG_neg_inv {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (t : ℝ) :
    (expG ε (-X) t)⁻¹ = expG ε X t := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  apply Units.ext
  show umat (expG ε (-X) t) * umat (expG ε X t) = 1
  rw [umat_expG (inG_neg hX), umat_expG hX]
  have : (t : ℂ) • (-X) = ((-t : ℝ) : ℂ) • X := by simp
  rw [this, exp_neg_mul_exp]

theorem test_add {Φ Φ' : Matrix (Fin n) (Fin n) ℂ → ℂ} (h : IsTest Φ) (h' : IsTest Φ') : IsTest (Φ + Φ') :=
  ⟨h.1.add h'.1, h.2.add h'.2⟩

theorem test_smul {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ) (h : IsTest Φ) : IsTest (c • Φ) :=
  ⟨contDiff_const.smul h.1, h.2.smul_left⟩

theorem test_zero : IsTest (0 : Matrix (Fin n) (Fin n) ℂ → ℂ) :=
  ⟨contDiff_const, HasCompactSupport.zero⟩

variable [CompleteSpace H]

def Vsub (ε : Fin n → Bool) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H) :
    Submodule ℂ H where
  carrier := {x | ∃ Φ, IsTest Φ ∧ x = vec ε σ w Φ}
  add_mem' := by
    rintro _ _ ⟨Φ, hΦ, rfl⟩ ⟨Φ', hΦ', rfl⟩
    refine ⟨Φ + Φ', test_add hΦ hΦ', ?_⟩
    unfold vec
    rw [← integral_add (vec_integrable hσ w hΦ) (vec_integrable hσ w hΦ')]
    congr 1
    funext y
    simp [add_smul]
  zero_mem' := ⟨0, test_zero, by simp [vec]⟩
  smul_mem' := by
    rintro c _ ⟨Φ, hΦ, rfl⟩
    refine ⟨c • Φ, test_smul c hΦ, ?_⟩
    unfold vec
    rw [← integral_smul]
    congr 1
    funext y
    simp [smul_smul]

theorem Vsub_stable {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H) (g : UJ ε)
    {x : H} (hx : x ∈ Vsub ε hσ w) : σ (umat g) x ∈ Vsub ε hσ w := by
  obtain ⟨Φ, hΦ, rfl⟩ := hx
  refine ⟨ltr (umat g⁻¹) Φ, test_ltr hΦ _, ?_⟩
  have := rep_vec hσ w hΦ g⁻¹
  rwa [inv_inv] at this

theorem Vsub_deriv {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H)
    {x : H} (hx : x ∈ Vsub ε hσ w) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    ∃ x' ∈ Vsub ε hσ w, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) x) x' 0 := by
  obtain ⟨Φ, hΦ, rfl⟩ := hx
  refine ⟨vec ε σ w (der (-X) Φ), ⟨_, test_der hΦ _, rfl⟩, ?_⟩
  have h := hasDerivAt_vec hσ w hΦ (inG_neg hX)
  refine h.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  show σ (NormedSpace.exp ((t : ℂ) • X)) (vec ε σ w Φ) = vec ε σ w (ltr (NormedSpace.exp ((t : ℂ) • (-X))) Φ)
  rw [← umat_expG (inG_neg hX) t, ← rep_vec hσ w hΦ, expG_neg_inv hX, umat_expG hX]

theorem Vsub_bound {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H)
    {A C0 : ℝ} (hA : 0 ≤ A) (hC0 : 0 ≤ C0)
    (hdec : ∀ g : UJ ε, ‖⟪w, σ (umat g) w⟫_ℂ‖ ≤ C0 * Real.sqrt (hs (umat g)) ^ (-A))
    {x x' : H} (hx : x ∈ Vsub ε hσ w) (hx' : x' ∈ Vsub ε hσ w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : UJ ε, ‖⟪x', σ (umat g) x⟫_ℂ‖ ≤ C * Real.sqrt (hs (umat g)) ^ (-A) := by
  obtain ⟨Φ, hΦ, rfl⟩ := hx
  obtain ⟨Φ', hΦ', rfl⟩ := hx'
  exact coef_bound hσ w hA hC0 hdec hΦ hΦ'

end Cls

section Smooth

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def mulB (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) ≃ₗ[ℝ] _).toLinearMap.comp
      (LinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)))

@[simp] theorem mulB_apply (a b : Matrix (Fin n) (Fin n) ℂ) : mulB n a b = a * b := rfl

theorem ContDiff.mmul {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {f g : P → Matrix (Fin n) (Fin n) ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun p => f p * g p) :=
by
  show ContDiff ℝ ∞ (fun p => (mulB n (f p)) (g p))
  exact ((mulB n).contDiff.comp hf).clm_apply hg

def sharpL (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => Jm ε * pᴴ * Jm ε
      map_add' := fun p q => by simp [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r p => by
        simp [Matrix.conjTranspose_smul] }

@[simp] theorem sharpL_apply (p : Matrix (Fin n) (Fin n) ℂ) : sharpL ε p = Jm ε * pᴴ * Jm ε := rfl

theorem umat_inv_eq (a : UJ ε) : umat a⁻¹ = sharpL ε (umat a) := by
  have h3 : umat a⁻¹ * umat a = 1 := by
    show umat (a⁻¹ * a) = 1
    rw [inv_mul_cancel]; rfl
  have h4 := (indefinite_unitary_inv_closed n ε (umat a) (umat_mem a)).1
  calc umat a⁻¹ = umat a⁻¹ * (umat a * (Jm ε * (umat a)ᴴ * Jm ε)) := by rw [h4, Matrix.mul_one]
    _ = Jm ε * (umat a)ᴴ * Jm ε := by rw [← Matrix.mul_assoc, h3, Matrix.one_mul]

@[reducible] def msM (n : ℕ) : MeasurableSpace (Matrix (Fin n) (Fin n) ℂ) := borel _
attribute [local instance] msM
local instance : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
local instance : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩
local instance : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.proper ℝ _

theorem locInt_coef {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (u w : H) :
    LocallyIntegrable (fun m : Matrix (Fin n) (Fin n) ℂ => ⟪u, σ m w⟫_ℂ) ((muG ε).map (fun y : UJ ε => umat y)) := by
  have hemb : MeasurableEmbedding (fun y : UJ ε => umat y) := (isClosedEmbeddingMatrix n ε).1.measurableEmbedding
  rw [locallyIntegrable_iff]
  intro k hk
  rw [hemb.integrableOn_map_iff]
  have hc : Continuous (fun y : UJ ε => ⟪u, σ (umat y) w⟫_ℂ) := continuous_const.inner (cont_orbit hσ w)
  exact hc.continuousOn.integrableOn_compact ((isClosedEmbeddingMatrix n ε).1.isCompact_preimage hk)

variable [CompleteSpace H]

theorem coef_eq_integral {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (u w : H)
    {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) (g : UJ ε) :
    ⟪u, σ (umat g) (vec ε σ w Φ)⟫_ℂ =
      ∫ y : UJ ε, Φ (sharpL ε (umat g) * umat y) • ⟪u, σ (umat y) w⟫_ℂ ∂(muG ε) := by
  have h1 := rep_vec hσ w hΦ g⁻¹
  rw [inv_inv] at h1
  rw [h1, vec, ← integral_inner (vec_integrable hσ w (test_ltr hΦ _))]
  congr 1
  funext y
  rw [inner_smul_right, umat_inv_eq]
  rfl

theorem smooth_coef {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (u w : H)
    {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) :
    Formalism.QuantumDeterminants.SmoothOnH (Jm ε) (fun g => ⟪u, σ g (vec ε σ w Φ)⟫_ℂ) := by
  intro g₀ _

  let 𝒦 : Set (Matrix (Fin n) (Fin n) ℂ) :=
    (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2) ''
      (Metric.closedBall g₀ 1 ×ˢ tsupport Φ)
  have h𝒦 : IsCompact 𝒦 :=
    ((isCompact_closedBall g₀ 1).prod hΦ.2.isCompact).image (continuous_fst.matrix_mul continuous_snd)
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ 𝒦 ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := h𝒦.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  let χ : ContDiffBump (0 : Matrix (Fin n) (Fin n) ℂ) := ⟨R, R + 1, hR0, by linarith⟩
  let Ψ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℂ := fun p y => (χ y : ℂ) * Φ (sharpL ε p * y)
  have hΨ : ContDiff ℝ ∞ (Function.uncurry Ψ) := by
    apply ContDiff.mul
    · exact Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp contDiff_snd)
    · exact hΦ.1.comp (ContDiff.mmul ((sharpL ε).contDiff.comp contDiff_fst) contDiff_snd)
  have key := contDiff_param_integral (hB := (⟨rfl⟩ : @BorelSpace _ _ (msM n))) (locInt_coef hσ u w) (Ψ := Ψ) (k := tsupport χ) χ.hasCompactSupport.isCompact
    (fun p x hx => by
      have : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [Ψ, this]) hΨ
  refine ⟨Metric.ball g₀ 1, _, Metric.isOpen_ball, Metric.mem_ball_self one_pos, key.contDiffOn, ?_⟩
  intro g hg hgU
  obtain ⟨γ, rfl⟩ : ∃ γ : UJ ε, umat γ = g := by
    have : g ∈ Set.range (fun y : UJ ε => umat y) := by rw [(isClosedEmbeddingMatrix n ε).2]; exact hgU
    exact this
  show ⟪u, σ (umat γ) (vec ε σ w Φ)⟫_ℂ = _
  rw [coef_eq_integral hσ u w hΦ γ, (isClosedEmbeddingMatrix n ε).1.integral_map]
  congr 1
  funext y
  show _ = ((χ (umat y) : ℂ) * Φ (sharpL ε (umat γ) * umat y)) • _
  by_cases h0 : Φ (sharpL ε (umat γ) * umat y) = 0
  · rw [h0]; simp
  · have hy : umat y ∈ 𝒦 := by
      refine ⟨(umat γ, sharpL ε (umat γ) * umat y), ⟨Metric.ball_subset_closedBall hg, subset_tsupport _ h0⟩, ?_⟩
      show umat γ * (sharpL ε (umat γ) * umat y) = umat y
      rw [← Matrix.mul_assoc, ← umat_inv_eq]
      have : umat γ * umat γ⁻¹ = umat (γ * γ⁻¹) := rfl
      rw [this, mul_inv_cancel]; exact Matrix.one_mul _
    have : χ (umat y) = 1 := χ.one_of_mem_closedBall (hR hy)
    rw [this]; simp

end Smooth

section KAvg

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

attribute [local instance] msM
local instance : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩
local instance : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
local instance : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.proper ℝ _

theorem closedEmb_toMK : Topology.IsClosedEmbedding (fun k : KG ε => toMK k) := by
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  refine ⟨hemb, ?_⟩
  rw [range_toMK]
  exact (maximal_compact_facts n ε).2.1.isClosed

def kconv (ε : Fin n → Bool) (e : KG ε → ℂ) (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun m => ∫ k : KG ε, e k * Φ (sharpL ε (toMK k) * m) ∂(muK ε)

theorem test_kconv {e : KG ε → ℂ} (he : Continuous e) {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) :
    IsTest (kconv ε e Φ) := by
  have hK : IsCompact (Kset ε) := (maximal_compact_facts n ε).2.1
  constructor
  · obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ Kset ε ⊆ Metric.closedBall 0 R := by
      obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
      exact ⟨max R 1, by positivity, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
    let χ : ContDiffBump (0 : Matrix (Fin n) (Fin n) ℂ) := ⟨R, R + 1, hR0, by linarith⟩
    let Ψ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℂ := fun p y => (χ y : ℂ) * Φ (sharpL ε y * p)
    have hΨ : ContDiff ℝ ∞ (Function.uncurry Ψ) := by
      apply ContDiff.mul
      · exact Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp contDiff_snd)
      · exact hΦ.1.comp (ContDiff.mmul ((sharpL ε).contDiff.comp contDiff_snd) contDiff_fst)
    let f : Matrix (Fin n) (Fin n) ℂ → ℂ := Function.extend (fun k : KG ε => toMK k) e 0
    have hinj : Function.Injective (fun k : KG ε => toMK k) := closedEmb_toMK.injective
    have hf : LocallyIntegrable f ((muK ε).map (fun k : KG ε => toMK k)) := by
      rw [locallyIntegrable_iff]
      intro k hk
      rw [closedEmb_toMK.measurableEmbedding.integrableOn_map_iff]
      have : f ∘ (fun k : KG ε => toMK k) = e := by
        funext k
        exact hinj.extend_apply e 0 k
      rw [this]
      exact he.continuousOn.integrableOn_compact (closedEmb_toMK.isCompact_preimage hk)
    have key := contDiff_param_integral (hB := (⟨rfl⟩ : @BorelSpace _ _ (msM n))) hf (Ψ := Ψ) (k := tsupport χ)
      χ.hasCompactSupport.isCompact
      (fun p x hx => by
        have : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [Ψ, this]) hΨ
    have e1 : kconv ε e Φ = fun p => ∫ y, Ψ p y • f y ∂((muK ε).map (fun k : KG ε => toMK k)) := by
      funext p
      rw [closedEmb_toMK.integral_map]
      unfold kconv
      congr 1
      funext k
      have h1 : χ (toMK k) = 1 := χ.one_of_mem_closedBall (hR k.2)
      have h2 : f (toMK k) = e k := hinj.extend_apply e 0 k
      show _ = ((χ (toMK k) : ℂ) * Φ (sharpL ε (toMK k) * p)) • f (toMK k)
      rw [h1, h2]
      simp [mul_comm]
    rw [e1]
    exact key
  · apply HasCompactSupport.intro
      ((hK.prod hΦ.2.isCompact).image (continuous_fst.matrix_mul continuous_snd))
    intro m hm
    unfold kconv
    have : ∀ k : KG ε, e k * Φ (sharpL ε (toMK k) * m) = 0 := by
      intro k
      by_contra hne
      apply hm
      have hne' : Φ (sharpL ε (toMK k) * m) ≠ 0 := fun h => hne (by rw [h, mul_zero])
      refine ⟨(toMK k, sharpL ε (toMK k) * m), ⟨k.2, subset_tsupport _ hne'⟩, ?_⟩
      show toMK k * (sharpL ε (toMK k) * m) = m
      rw [← Matrix.mul_assoc]
      have := (indefinite_unitary_inv_closed n ε (toMK k) (umat_mem (k : UJ ε))).1
      rw [sharpL_apply, this, Matrix.one_mul]
    simp_rw [this]
    simp

variable [CompleteSpace H]

theorem kavg_integrable {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {e : KG ε → ℂ} (he : Continuous e) (v : H) :
    Integrable (fun k : KG ε => e k • σ (toMK k) v) (muK ε) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact he.smul ((cont_orbit hσ v).comp continuous_subtype_val)
  · exact HasCompactSupport.of_compactSpace _

def kavg {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {e : KG ε → ℂ} (he : Continuous e) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun v => ∫ k : KG ε, e k • σ (toMK k) v ∂(muK ε)
      map_add' := fun v v' => by
        rw [← integral_add (kavg_integrable hσ he v) (kavg_integrable hσ he v')]
        congr 1; funext k; simp [smul_add]
      map_smul' := fun c v => by
        simp only [RingHom.id_apply]
        rw [← integral_smul]
        congr 1; funext k; simp [smul_comm c] }
    (∫ k : KG ε, ‖e k‖ ∂(muK ε))
    (fun v => by
      show ‖∫ k : KG ε, e k • σ (toMK k) v ∂(muK ε)‖ ≤ _
      refine le_trans (norm_integral_le_integral_norm _) ?_
      rw [← integral_mul_const]
      apply le_of_eq
      congr 1; funext k
      rw [norm_smul, hσ.2.1 _ (umat_mem (k : UJ ε))])

theorem kavg_apply {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    {e : KG ε → ℂ} (he : Continuous e) (v : H) :
    kavg hσ he v = ∫ k : KG ε, e k • σ (toMK k) v ∂(muK ε) := rfl

theorem kavg_vec {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H)
    {e : KG ε → ℂ} (he : Continuous e) {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) :
    kavg hσ he (vec ε σ w Φ) = vec ε σ w (kconv ε e Φ) := by
  have hK : IsCompact (Kset ε) := (maximal_compact_facts n ε).2.1
  rw [kavg_apply]
  have h1 : ∀ k : KG ε, e k • σ (toMK k) (vec ε σ w Φ) =
      ∫ y : UJ ε, (e k * Φ (sharpL ε (toMK k) * umat y)) • σ (umat y) w ∂(muG ε) := by
    intro k
    have h2 := rep_vec hσ w hΦ (k : UJ ε)⁻¹
    rw [inv_inv] at h2
    have h3 : toMK k = umat (k : UJ ε) := rfl
    rw [h3, h2, vec, ← integral_smul]
    congr 1; funext y
    rw [smul_smul, umat_inv_eq]
    rfl
  simp_rw [h1]
  rw [integral_integral_swap]
  · unfold vec kconv
    congr 1; funext y
    rw [integral_smul_const]
  · apply Continuous.integrable_of_hasCompactSupport
    · apply Continuous.smul
      · apply Continuous.mul (he.comp continuous_fst)
        apply hΦ.1.continuous.comp
        apply Continuous.matrix_mul
        · exact (sharpL ε).continuous.comp (closedEmb_toMK.continuous.comp continuous_fst)
        · exact continuous_umat.comp continuous_snd
      · exact (cont_orbit hσ w).comp continuous_snd
    · have hc : IsCompact ((fun y : UJ ε => umat y) ⁻¹'
          ((fun x : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => x.1 * x.2) '' Kset ε ×ˢ tsupport Φ)) :=
        (isClosedEmbeddingMatrix n ε).1.isCompact_preimage
          ((hK.prod hΦ.2.isCompact).image (continuous_fst.matrix_mul continuous_snd))
      apply HasCompactSupport.intro (isCompact_univ.prod hc)
      rintro ⟨k, y⟩ hky
      have : Φ (sharpL ε (toMK k) * umat y) = 0 := by
        by_contra hne
        apply hky
        refine ⟨Set.mem_univ _, (toMK k, sharpL ε (toMK k) * umat y), ⟨k.2, subset_tsupport _ hne⟩, ?_⟩
        show toMK k * (sharpL ε (toMK k) * umat y) = umat y
        rw [← Matrix.mul_assoc]
        have := (indefinite_unitary_inv_closed n ε (toMK k) (umat_mem (k : UJ ε))).1
        rw [sharpL_apply, this, Matrix.one_mul]
      show (e k * Φ (sharpL ε (toMK k) * umat y)) • σ (umat y) w = 0
      rw [this]; simp

end KAvg

section Claim

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.proper ℝ _

theorem Vsub_ne_bot {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {w : H} (hw : w ≠ 0) :
    Vsub ε hσ w ≠ ⊥ := by
  have hc : Continuous (fun y : UJ ε => (⟪w, σ (umat y) w⟫_ℂ).re) :=
    Complex.continuous_re.comp (continuous_const.inner (cont_orbit hσ w))
  have hw2 : 0 < ‖w‖ ^ 2 := by positivity
  have h1 : (⟪w, σ (umat (1 : UJ ε)) w⟫_ℂ).re = ‖w‖ ^ 2 := by
    have : σ (umat (1 : UJ ε)) = 1 := hσ.1.1
    rw [this]
    simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  let U : Set (UJ ε) := {y | 0 < (⟪w, σ (umat y) w⟫_ℂ).re}
  have hU : IsOpen U := isOpen_lt continuous_const hc
  obtain ⟨V, hV, hVU⟩ := (isClosedEmbeddingMatrix n ε).1.isInducing.isOpen_iff.1 hU
  have h1V : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ V := by
    have : (1 : UJ ε) ∈ U := by
      show 0 < (⟪w, σ (umat (1 : UJ ε)) w⟫_ℂ).re
      rw [h1]; exact hw2
    rw [← hVU] at this
    exact this
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hV 1 h1V
  let χ : ContDiffBump (1 : Matrix (Fin n) (Fin n) ℂ) := ⟨δ / 2, δ, by positivity, by linarith⟩
  let Φ : Matrix (Fin n) (Fin n) ℂ → ℂ := fun m => (χ m : ℂ)
  have hΦ : IsTest Φ := by
    refine ⟨Complex.ofRealCLM.contDiff.comp χ.contDiff, ?_⟩
    exact χ.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  intro hbot
  have hz : vec ε σ w Φ = 0 := by
    have : vec ε σ w Φ ∈ Vsub ε hσ w := ⟨Φ, hΦ, rfl⟩
    rw [hbot] at this
    exact this
  have e1 : (⟪w, vec ε σ w Φ⟫_ℂ).re = ∫ y : UJ ε, χ (umat y) * (⟪w, σ (umat y) w⟫_ℂ).re ∂(muG ε) := by
    rw [vec, ← integral_inner (vec_integrable hσ w hΦ)]
    have hint : Integrable (fun y : UJ ε => ⟪w, Φ (umat y) • σ (umat y) w⟫_ℂ) (muG ε) :=
      (vec_integrable hσ w hΦ).const_inner w
    have := integral_re hint
    rw [← RCLike.re_eq_complex_re, ← this]
    congr 1; funext y
    rw [inner_smul_right]
    simp [Φ]
  rw [hz, inner_zero_right] at e1
  have hpos : 0 < ∫ y : UJ ε, χ (umat y) * (⟪w, σ (umat y) w⟫_ℂ).re ∂(muG ε) := by
    apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (1 : UJ ε))
    · exact (χ.continuous.comp continuous_umat).mul hc
    · have : HasCompactSupport (fun y : UJ ε => χ (umat y)) :=
        χ.hasCompactSupport.comp_isClosedEmbedding (isClosedEmbeddingMatrix n ε).1
      exact this.mul_right
    · intro y
      show 0 ≤ χ (umat y) * _
      by_cases hy : χ (umat y) = 0
      · rw [hy, zero_mul]
      · have hy' : umat y ∈ Metric.ball (1 : Matrix (Fin n) (Fin n) ℂ) δ := by
          have : umat y ∈ Function.support χ := hy
          rwa [χ.support_eq] at this
        have : y ∈ U := by rw [← hVU]; exact hball hy'
        exact mul_nonneg χ.nonneg (le_of_lt this)
    · show χ (umat (1 : UJ ε)) * _ ≠ 0
      rw [h1]
      have : χ (umat (1 : UJ ε)) = 1 := χ.one_of_mem_closedBall (by
        have : umat (1 : UJ ε) = 1 := rfl
        rw [this]
        exact Metric.mem_closedBall_self χ.rIn_pos.le)
      rw [this]; positivity
  simp at e1
  linarith [hpos, e1]

theorem Vsub_dense {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) {w : H} (hw : w ≠ 0) : (Vsub ε hσ w).topologicalClosure = ⊤ := by
  have hst : ∀ g ∈ UJset ε, ∀ v ∈ (Vsub ε hσ w).topologicalClosure, σ g v ∈ (Vsub ε hσ w).topologicalClosure := by
    intro g hg v hv
    obtain ⟨γ, rfl⟩ : ∃ γ : UJ ε, umat γ = g := by
      have : g ∈ Set.range (fun y : UJ ε => umat y) := by rw [(isClosedEmbeddingMatrix n ε).2]; exact hg
      exact this
    exact map_mem_closure (σ (umat γ)).continuous hv (fun x hx => Vsub_stable hσ w γ hx)
  rcases hirr (Vsub ε hσ w).topologicalClosure (Vsub ε hσ w).isClosed_topologicalClosure hst with h | h
  · exfalso
    apply Vsub_ne_bot hσ hw
    exact eq_bot_iff.2 (h ▸ (Vsub ε hσ w).le_topologicalClosure)
  · exact h

def AdmProjAt (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x : H, IsKFin ε σ x → ∃ (e : KG ε → ℂ) (T : Submodule ℂ H), Continuous e ∧ FiniteDimensional ℂ T ∧
    (∀ v : H, ∫ k : KG ε, e k • σ (toMK k) v ∂(muK ε) ∈ T) ∧ ∫ k : KG ε, e k • σ (toMK k) x ∂(muK ε) = x

theorem kfin_mem_Vsub {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) (hadm : AdmProjAt ε σ) {w : H} (hw : w ≠ 0) {x : H} (hx : IsKFin ε σ x) :
    x ∈ Vsub ε hσ w := by
  obtain ⟨e, T, he, hT, hrange, hfix⟩ := hadm x hx
  let T₀ : Submodule ℂ H := (Vsub ε hσ w).map (kavg hσ he : H →ₗ[ℂ] H)
  have hle : T₀ ≤ T := by
    rintro _ ⟨v, _, rfl⟩
    exact hrange v
  have : FiniteDimensional ℂ T₀ := Submodule.finiteDimensional_of_le hle
  have hcl : IsClosed (T₀ : Set H) := Submodule.closed_of_finiteDimensional T₀
  have hxc : x ∈ closure (Vsub ε hσ w : Set H) := by
    have := Vsub_dense hσ hirr hw
    have h2 : x ∈ (Vsub ε hσ w).topologicalClosure := by rw [this]; trivial
    exact h2
  have h3 : kavg hσ he x ∈ closure (T₀ : Set H) :=
    map_mem_closure (kavg hσ he).continuous hxc (fun v hv => ⟨v, hv, rfl⟩)
  rw [hcl.closure_eq, kavg_apply, hfix] at h3
  obtain ⟨v, ⟨Φ, hΦ, rfl⟩, hv⟩ := h3
  refine ⟨kconv ε e Φ, test_kconv he hΦ, ?_⟩
  rw [← kavg_vec hσ w he hΦ]
  exact hv.symm

end Claim

section Model

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def cj (Pc g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Pc * g * Pcᴴ

def IsCay (ε : Fin n → Bool) (Hm Pc : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Pc ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ Pcᴴ * Jm ε * Pc = Hm

variable {Hm Pc : Matrix (Fin n) (Fin n) ℂ}

theorem cay1 (hP : IsCay ε Hm Pc) : Pcᴴ * Pc = 1 := Matrix.mem_unitaryGroup_iff'.1 hP.1
theorem cay2 (hP : IsCay ε Hm Pc) : Pc * Pcᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hP.1

theorem cj_mul (hP : IsCay ε Hm Pc) (a b : Matrix (Fin n) (Fin n) ℂ) : cj Pc (a * b) = cj Pc a * cj Pc b := by
  unfold cj
  calc Pc * (a * b) * Pcᴴ = Pc * a * 1 * b * Pcᴴ := by simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Pc * a * Pcᴴ * (Pc * b * Pcᴴ) := by rw [← cay1 hP]; simp only [Matrix.mul_assoc]

theorem cj_mem (hP : IsCay ε Hm Pc) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH Hm) :
    inUJ ε (cj Pc g) := by
  have hg' : gᴴ * Hm * g = Hm := hg
  unfold inUJ cj
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc Pc * (gᴴ * Pcᴴ) * Jm ε * (Pc * g * Pcᴴ) = Pc * (gᴴ * (Pcᴴ * Jm ε * Pc) * g) * Pcᴴ := by
        simp only [Matrix.mul_assoc]
    _ = Pc * (Pcᴴ * Jm ε * Pc) * Pcᴴ := by rw [hP.2, hg']
    _ = (Pc * Pcᴴ) * Jm ε * (Pc * Pcᴴ) := by simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [cay2 hP, Matrix.one_mul, Matrix.mul_one]

theorem cj_lie (hP : IsCay ε Hm Pc) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * Hm + Hm * X = 0) :
    inG ε (cj Pc X) := by
  unfold inG cj
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc Pc * (Xᴴ * Pcᴴ) * Jm ε + Jm ε * (Pc * X * Pcᴴ)
      = Pc * (Xᴴ * (Pcᴴ * Jm ε * Pc)) * Pcᴴ + Pc * ((Pcᴴ * Jm ε * Pc) * X) * Pcᴴ := by
        have e1 : Pc * (Xᴴ * (Pcᴴ * Jm ε * Pc)) * Pcᴴ = Pc * (Xᴴ * Pcᴴ) * Jm ε * (Pc * Pcᴴ) := by
          simp only [Matrix.mul_assoc]
        have e2 : Pc * ((Pcᴴ * Jm ε * Pc) * X) * Pcᴴ = (Pc * Pcᴴ) * Jm ε * (Pc * X * Pcᴴ) := by
          simp only [Matrix.mul_assoc]
        rw [e1, e2, cay2 hP, Matrix.mul_one, Matrix.one_mul]
    _ = Pc * (Xᴴ * Hm + Hm * X) * Pcᴴ := by rw [hP.2, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX]; simp

theorem cj_exp (hP : IsCay ε Hm Pc) (A : Matrix (Fin n) (Fin n) ℂ) :
    cj Pc (NormedSpace.exp A) = NormedSpace.exp (cj Pc A) := by
  have hu : IsUnit Pc := ⟨⟨Pc, Pcᴴ, cay2 hP, cay1 hP⟩, rfl⟩
  have hinv : Pc⁻¹ = Pcᴴ := Matrix.inv_eq_left_inv (cay1 hP)
  have := Matrix.exp_conj Pc A hu
  rw [hinv] at this
  exact this.symm

theorem cj_smul (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) : cj Pc (c • A) = c • cj Pc A := by
  unfold cj; simp

theorem exists_UJ {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : ∃ γ : UJ ε, umat γ = g := by
  have : g ∈ Set.range (fun y : UJ ε => umat y) := by rw [(isClosedEmbeddingMatrix n ε).2]; exact hg
  exact this

theorem UH_mul_exp (hP : IsCay ε Hm Pc) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH Hm)
    (hX : Xᴴ * Hm + Hm * X = 0) (t : ℝ) :
    ∃ γ : UJ ε, umat γ = cj Pc g ∧
      cj Pc (g * NormedSpace.exp ((t : ℂ) • X)) = umat (γ * expG ε (cj Pc X) t) := by
  obtain ⟨γ, hγ⟩ := exists_UJ (cj_mem hP hg)
  refine ⟨γ, hγ, ?_⟩
  show _ = umat γ * umat (expG ε (cj Pc X) t)
  rw [cj_mul hP, cj_exp hP, cj_smul, hγ, umat_expG (cj_lie hP hX)]

theorem mem_of_cj (hP : IsCay ε Hm Pc) {h : Matrix (Fin n) (Fin n) ℂ} (hh : inUJ ε (cj Pc h)) :
    h ∈ Formalism.QuantumDeterminants.UH Hm := by
  unfold inUJ cj at hh
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at hh
  show hᴴ * Hm * h = Hm
  have e1 : Pc * (hᴴ * Pcᴴ) * Jm ε * (Pc * h * Pcᴴ) = Pc * (hᴴ * (Pcᴴ * Jm ε * Pc) * h) * Pcᴴ := by
    simp only [Matrix.mul_assoc]
  rw [e1, hP.2] at hh
  calc hᴴ * Hm * h = (Pcᴴ * Pc) * (hᴴ * Hm * h) * (Pcᴴ * Pc) := by rw [cay1 hP]; simp
    _ = Pcᴴ * (Pc * (hᴴ * Hm * h) * Pcᴴ) * Pc := by simp only [Matrix.mul_assoc]
    _ = Hm := by rw [hh, hP.2]

theorem UH_mul_exp' (hP : IsCay ε Hm Pc) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH Hm)
    (hX : Xᴴ * Hm + Hm * X = 0) (t : ℝ) : g * NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.UH Hm := by
  obtain ⟨γ, _, h2⟩ := UH_mul_exp hP hg hX t
  apply mem_of_cj hP
  rw [h2]
  exact umat_mem _

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def Cls (Hm Pc : Matrix (Fin n) (Fin n) ℂ) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (w : H) (F : Matrix (Fin n) (Fin n) ℂ → V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (x' x : ι → H) (c : ι → V), (∀ i, x' i ∈ Vsub ε hσ w) ∧ (∀ i, x i ∈ Vsub ε hσ w) ∧
    ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, F g = ∑ i, ⟪x' i, σ (cj Pc g) (x i)⟫_ℂ • c i

theorem Cls_rdM (hP : IsCay ε Hm Pc) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (w : H) {F : Matrix (Fin n) (Fin n) ℂ → V} (hF : Cls Hm Pc hσ w F) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * Hm + Hm * X = 0) : Cls Hm Pc hσ w (rdM X F) := by
  obtain ⟨ι, _, x', x, c, hx', hx, hF⟩ := hF
  choose y hy hder using fun i => Vsub_deriv hσ w (hx i) (cj_lie hP hX)
  refine ⟨ι, inferInstance, x', y, c, hx', hy, fun g hg => ?_⟩
  unfold rdM
  obtain ⟨γ, hγ⟩ := exists_UJ (cj_mem hP hg)
  have hmem : ∀ t : ℝ, g * NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.UH Hm := fun t => UH_mul_exp' hP hg hX t
  have e1 : (fun t : ℝ => F (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => ∑ i, ((innerSL ℂ (x' i)).comp (σ (umat γ))) (σ (NormedSpace.exp ((t : ℂ) • cj Pc X)) (x i)) • c i := by
    funext t
    rw [hF _ (hmem t)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [cj_mul hP, cj_exp hP, cj_smul, ← hγ, ← umat_expG (cj_lie hP hX) t]
    have := rep_mul hσ γ (expG ε (cj Pc X) t) (x i)
    show ⟪x' i, σ (umat γ * umat (expG ε (cj Pc X) t)) (x i)⟫_ℂ = _
    have h2 : umat γ * umat (expG ε (cj Pc X) t) = umat (γ * expG ε (cj Pc X) t) := rfl
    rw [h2, this]
    rfl
  rw [e1]
  have hd : HasDerivAt (fun t : ℝ => ∑ i, ((innerSL ℂ (x' i)).comp (σ (umat γ)))
      (σ (NormedSpace.exp ((t : ℂ) • cj Pc X)) (x i)) • c i)
      (∑ i, ((innerSL ℂ (x' i)).comp (σ (umat γ))) (y i) • c i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    have h3 := ((innerSL ℂ (x' i)).comp (σ (umat γ))).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder i)
    exact h3.smul_const (c i)
  rw [hd.deriv, ← hγ]
  rfl

end Model

section Model2

open Formalism.MainNotions.BridgeLemma

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Hm Pc : Matrix (Fin n) (Fin n) ℂ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Cls_rdWord (hP : IsCay ε Hm Pc) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (w : H) {F : Matrix (Fin n) (Fin n) ℂ → V} (hF : Cls Hm Pc hσ w F) :
    ∀ ws : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ ws, Xᴴ * Hm + Hm * X = 0) → Cls Hm Pc hσ w (rdWord ws F)
  | [], _ => hF
  | X :: ws, h => Cls_rdM hP hσ w (Cls_rdWord hP hσ w hF ws fun Y hY => h Y (List.mem_cons_of_mem _ hY))
      (h X List.mem_cons_self)

theorem Cls_bound (hP : IsCay ε Hm Pc) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (w : H) {A C0 : ℝ} (hA : 0 ≤ A) (hC0 : 0 ≤ C0)
    (hdec : ∀ g : UJ ε, ‖⟪w, σ (umat g) w⟫_ℂ‖ ≤ C0 * Real.sqrt (hs (umat g)) ^ (-A))
    {F : Matrix (Fin n) (Fin n) ℂ → V} (hF : Cls Hm Pc hσ w F) :
    ∃ C : ℝ, ∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ‖F g‖ ≤ C * Real.sqrt (hs g) ^ (-A) := by
  obtain ⟨ι, _, x', x, c, hx', hx, hF⟩ := hF
  choose C hC0' hC using fun i => Vsub_bound hσ w hA hC0 hdec (hx i) (hx' i)
  refine ⟨∑ i, C i * ‖c i‖, fun g hg => ?_⟩
  obtain ⟨γ, hγ⟩ := exists_UJ (cj_mem hP hg)
  have hhs : hs (umat γ) = hs g := by rw [hγ]; exact hs_unitary_conj Pc g hP.1
  rw [hF g hg, Finset.sum_mul]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_smul, ← hγ]
  have := hC i γ
  rw [hhs] at this
  calc ‖⟪x' i, σ (umat γ) (x i)⟫_ℂ‖ * ‖c i‖ ≤ (C i * Real.sqrt (hs g) ^ (-A)) * ‖c i‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = _ := by ring

def cjL (Pc : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (rmulL Pcᴴ).comp (lmulL Pc)

theorem cjL_apply (g : Matrix (Fin n) (Fin n) ℂ) : cjL Pc g = cj Pc g := rfl

theorem Cls_smooth (hP : IsCay ε Hm Pc) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (w : H) {F : Matrix (Fin n) (Fin n) ℂ → V} (hF : Cls Hm Pc hσ w F) : Formalism.QuantumDeterminants.SmoothOnH Hm F := by
  obtain ⟨ι, _, x', x, c, hx', hx, hF⟩ := hF
  intro g₀ hg₀
  have hs : ∀ i, ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (G : Matrix (Fin n) (Fin n) ℂ → ℂ),
      IsOpen U ∧ cj Pc g₀ ∈ U ∧ ContDiffOn ℝ ∞ G U ∧ ∀ g ∈ U, Formalism.QuantumDeterminants.inUH (Jm ε) g →
        ⟪x' i, σ g (x i)⟫_ℂ = G g := by
    intro i
    obtain ⟨Φ, hΦ, hxi⟩ := hx i
    rw [hxi]
    exact smooth_coef hσ (x' i) w hΦ (cj Pc g₀) (cj_mem hP hg₀)
  choose U G hU hmem hG hagree using hs
  refine ⟨⋂ i, (cjL Pc) ⁻¹' (U i), fun g => ∑ i, G i (cjL Pc g) • c i, ?_, ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun i => (hU i).preimage (cjL Pc).continuous
  · exact Set.mem_iInter.2 fun i => hmem i
  · apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.smul _ contDiffOn_const
    apply (hG i).comp (cjL Pc).contDiff.contDiffOn
    intro g hg
    exact Set.mem_iInter.1 hg i
  · intro g hg hgU
    rw [hF g hgU]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hagree i (cj Pc g) (Set.mem_iInter.1 hg i) (cj_mem hP hgU)]
    rfl

end Model2

section Sig

open Formalism.MainNotions.BridgeLemma Formalism.MainNotions.PlaceDegreeData

theorem trace_Jm {n : ℕ} (ε : Fin n → Bool) : (Jm ε).trace = (pOf ε : ℂ) - (qOf ε : ℂ) := by
  unfold Jm Matrix.trace pOf qOf
  simp only [Matrix.diag_diagonal]
  have : ∀ a : Fin n, (if ε a = true then (1 : ℂ) else -1) =
      (if ε a = true then 1 else 0) - (if ε a = false then 1 else 0) := by
    intro a
    cases ε a <;> simp
  simp_rw [this]
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_boole]

theorem pOf_add_qOf {n : ℕ} (ε : Fin n → Bool) : pOf ε + qOf ε = n := by
  unfold pOf qOf
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n))) (fun a => ε a = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at this
  exact this

theorem trace_Hpk (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r).trace = (k : ℂ) - 1 := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply]
  have h1 : ∀ i : Fin (2 * r + k + 1), Formalism.QuantumDeterminants.Hpk k r i i =
      (if r ≤ i.val ∧ i.val < r + k then (1 : ℂ) else 0) - (if i.val = r + k then 1 else 0) := by
    intro i
    unfold Formalism.QuantumDeterminants.Hpk
    have := i.2
    split_ifs <;> first | omega | simp
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Fin.sum_univ_eq_sum_range (fun i => if r ≤ i ∧ i < r + k then (1 : ℂ) else 0),
    Fin.sum_univ_eq_sum_range (fun i => if i = r + k then (1 : ℂ) else 0)]
  rw [Finset.sum_boole, Finset.sum_boole]
  have e1 : (Finset.range (2 * r + k + 1)).filter (fun i => r ≤ i ∧ i < r + k) = Finset.Ico r (r + k) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  have e2 : (Finset.range (2 * r + k + 1)).filter (fun i => i = r + k) = {r + k} := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega
  rw [e1, e2]
  simp

theorem sig_of_cayley (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool)
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hP : IsCayleyU k r ε P) :
    pOf ε = r + k ∧ qOf ε = r + 1 := by
  have a2 : P * Pᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hP.2
  have h1 : (Jm ε).trace = (Formalism.QuantumDeterminants.Hpk k r).trace := by
    rw [← hP.1.2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, a2, Matrix.one_mul]
  rw [trace_Jm, trace_Hpk] at h1
  have h2 := pOf_add_qOf ε
  have h3 : ((pOf ε : ℤ) : ℂ) - ((qOf ε : ℤ) : ℂ) = ((k : ℤ) : ℂ) - 1 := by exact_mod_cast h1
  have h4 : (pOf ε : ℤ) - (qOf ε : ℤ) = (k : ℤ) - 1 := by exact_mod_cast h3
  omega

end Sig

section Final

open Formalism.MainNotions.BridgeLemma Formalism.MainNotions.PlaceDegreeData Formalism.BasicNotions

def HCAdm : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → AdmProjAt ε σ

def HCAdmDS : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → AdmProjAt ε σ

theorem HCAdmDS_of_HCAdm (h : HCAdm) : HCAdmDS :=
  fun n ε _ H _ _ _ σ hDS => h n ε H σ hDS.2.2.1 hDS.2.2.2.1

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem clm_expand {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (T : Wq →L[ℂ] Wp) :
    T = ∑ p : Fin (Module.finrank ℂ Wp) × Fin (Module.finrank ℂ Wq),
      ⟪stdOrthonormalBasis ℂ Wp p.1, T (stdOrthonormalBasis ℂ Wq p.2)⟫_ℂ •
        (innerSL ℂ (stdOrthonormalBasis ℂ Wq p.2)).smulRight (stdOrthonormalBasis ℂ Wp p.1) := by
  ext v
  rw [_root_.sum_apply, Fintype.sum_prod_type, Finset.sum_comm]
  conv_lhs => rw [← (stdOrthonormalBasis ℂ Wq).sum_repr' v, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  conv_lhs => rw [← (stdOrthonormalBasis ℂ Wp).sum_repr' (T (stdOrthonormalBasis ℂ Wq j)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_smul, mul_comm]

theorem coefT_Cls {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {Pc : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hPc : IsCayleyU k r ε Pc)
    (hσ : IsURepOn (UJset ε) (fun g => σ (Pc⁻¹ * g * Pc))) (hirr : IsIrredOn (UJset ε) (fun g => σ (Pc⁻¹ * g * Pc)))
    (hadm : AdmProjAt ε (fun g => σ (Pc⁻¹ * g * Pc))) {w : H} (hw : w ≠ 0)
    {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)} (hf : UnitaryLevelOperators.IsKFinCoefT σ f) :
    Cls (Formalism.QuantumDeterminants.Hpk k r) Pc hσ w f := by
  have hP : IsCay ε (Formalism.QuantumDeterminants.Hpk k r) Pc := ⟨hPc.2, hPc.1.2⟩
  have iP : Pc⁻¹ = Pcᴴ := Matrix.inv_eq_left_inv (cay1 hP)
  obtain ⟨a, ha, b, hb, P0, Q0, hQ, hP0, hfe⟩ := hf
  have kf : ∀ y : H, IsKFinHpk (k := k) (r := r) σ y → IsKFin ε (fun g => σ (Pc⁻¹ * g * Pc)) y := by
    rintro y ⟨S, hfd, hyS, hst⟩
    exact ⟨S, hfd, hyS, fun g hg u hu => hst _ (compact_to_unitary_hermitian _ _ _ Pc g hPc hg) u hu⟩
  obtain ⟨α, hα⟩ := exists_UJ (cj_mem hP ha)
  obtain ⟨β, hβ⟩ := exists_UJ (cj_mem hP hb)
  set σ' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H) := fun g => σ (Pc⁻¹ * g * Pc) with hσ'
  refine ⟨Fin (Module.finrank ℂ Wp) × Fin (Module.finrank ℂ Wq), inferInstance,
    fun p => σ' (umat α) (ContinuousLinearMap.adjoint P0 (stdOrthonormalBasis ℂ Wp p.1)),
    fun p => σ' (umat β⁻¹) (Q0 (stdOrthonormalBasis ℂ Wq p.2)),
    fun p => (innerSL ℂ (stdOrthonormalBasis ℂ Wq p.2)).smulRight (stdOrthonormalBasis ℂ Wp p.1), ?_, ?_, ?_⟩
  · intro p
    exact Vsub_stable hσ w α (kfin_mem_Vsub hσ hirr hadm hw (kf _ (hP0 _)))
  · intro p
    exact Vsub_stable hσ w β⁻¹ (kfin_mem_Vsub hσ hirr hadm hw (kf _ (hQ _)))
  · intro g hg
    obtain ⟨γ, hγ⟩ := exists_UJ (cj_mem hP hg)

    have back : ∀ m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Pcᴴ * cj Pc m * Pc = m := by
      intro m
      unfold cj
      calc Pcᴴ * (Pc * m * Pcᴴ) * Pc = (Pcᴴ * Pc) * m * (Pcᴴ * Pc) := by simp only [Matrix.mul_assoc]
        _ = m := by rw [cay1 hP]; simp
    set g' := Pcᴴ * umat (α⁻¹ * γ * β⁻¹) * Pc with hg'
    have e1 : a * g' * b = g := by
      rw [← back a, ← back b, ← back g, ← hα, ← hβ, ← hγ, hg']
      calc Pcᴴ * umat α * Pc * (Pcᴴ * umat (α⁻¹ * γ * β⁻¹) * Pc) * (Pcᴴ * umat β * Pc)
          = Pcᴴ * (umat α * (Pc * Pcᴴ) * umat (α⁻¹ * γ * β⁻¹) * (Pc * Pcᴴ) * umat β) * Pc := by
            simp only [Matrix.mul_assoc]
        _ = Pcᴴ * umat (α * (α⁻¹ * γ * β⁻¹) * β) * Pc := by
            rw [cay2 hP, Matrix.mul_one, Matrix.mul_one]; rfl
        _ = Pcᴴ * umat γ * Pc := by congr 3; group
    have e2 : f g = P0.comp ((σ' (umat (α⁻¹ * γ * β⁻¹))).comp Q0) := by
      rw [← e1]
      have := hfe g'
      simp only at this
      rw [this, hσ', hg', iP]
    rw [e2]
    conv_lhs => rw [clm_expand (P0.comp ((σ' (umat (α⁻¹ * γ * β⁻¹))).comp Q0))]
    refine Finset.sum_congr rfl fun p _ => ?_
    congr 1
    show ⟪stdOrthonormalBasis ℂ Wp p.1, P0 (σ' (umat (α⁻¹ * γ * β⁻¹)) (Q0 (stdOrthonormalBasis ℂ Wq p.2)))⟫_ℂ = _
    rw [← ContinuousLinearMap.adjoint_inner_left, rep_mul hσ, rep_mul hσ, rep_inner_left hσ α, hγ]

theorem stDecay_of (D : D7) {c C₁ : ℝ} (hc : 0 < c) (hc8 : c ≤ 1 / 8) (hC1 : 120 ≤ C₁)
    (ha2 : PlaceDegreeData.adm2 D) (h1 : PlaceDegreeData.DiscreteSeriesDecayBound D) (hadm : HCAdmDS) : UnitaryLevelOperators.stDecay D c C₁ := by
  have hsq2 : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  refine ⟨hc, by linarith, hC1, fun k0 hk L hgap f hf mm => ?_⟩
  obtain ⟨Pc, hPc, hDS⟩ := L.hσ
  have hP : IsCay L.ε (Formalism.QuantumDeterminants.Hpk (k0 + 1) D.R.rS) Pc := ⟨hPc.2, hPc.1.2⟩
  have hσ : IsURepOn (UJset L.ε) (fun g => L.σ (Pc⁻¹ * g * Pc)) := hDS.2.2.1
  have hirr : IsIrredOn (UJset L.ε) (fun g => L.σ (Pc⁻¹ * g * Pc)) := hDS.2.2.2.1
  obtain ⟨w, hw⟩ := exists_highest_weight_unit L.ε L.lam _ hDS
  have hw0 : w ≠ 0 := by
    intro h0
    have := hw.1
    rw [h0, norm_zero] at this
    norm_num at this
  have hlow : IsLowUnit L.ε L.lam (fun g => L.σ (Pc⁻¹ * g * Pc)) w := ⟨hw.1, hw.2.1⟩
  have : FiniteDimensional ℂ (lowKSub L.ε L.lam (fun g => L.σ (Pc⁻¹ * g * Pc))) :=
    (ha2 _ L.ε L.lam L.hlam L.Hs _ hDS).1.1
  have hE := star_projection_is_orth_proj (lowKSub L.ε L.lam (fun g => L.σ (Pc⁻¹ * g * Pc)))
  obtain ⟨hp, hq⟩ := sig_of_cayley (k0 + 1) D.R.rS L.ε Pc hPc
  set h : ℝ := UnitaryLevelOperators.ncGap L.ε L.lam with hh
  have hgapAt : Formalism.QuantumDeterminants.GapAtLeast L.ε L.lam h := fun a b hab =>
    csInf_le ⟨0, by rintro d ⟨a, b, _, rfl⟩; exact abs_nonneg _⟩ ⟨a, b, hab, rfl⟩
  have hmin : min (pOf L.ε) (qOf L.ε) = D.R.rS + 1 := by rw [hp, hq]; omega
  have hm := two_rS_add_two D
  have hmR : (2 : ℝ) * ((D.R.rS + 1 : ℕ) : ℝ) = (D.R.m : ℝ) := by rw [← hm]; push_cast; ring
  have hm2 : (2 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast D.R.two_le_m
  have hN : ((2 * D.R.rS + (k0 + 1) + 1 : ℕ) : ℝ) = (D.R.r : ℝ) := by rw [hk]; exact nS_cast D
  have hN6 := six_le_n D
  set N : ℝ := (D.R.r : ℝ) with hNdef
  set m : ℝ := (D.R.m : ℝ) with hmdef
  have hth : 120 * ((2 * D.R.rS + (k0 + 1) + 1 : ℕ) : ℝ) *
      ((min (pOf L.ε) (qOf L.ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [hmin, hN]
    refine le_trans ?_ hgap
    have hqm : ((D.R.rS + 1 : ℕ) : ℝ) = m / 2 := by linarith
    rw [hqm]
    have e0 : 0 ≤ (m / 2) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 (by linarith)) e0
  have hh0 : 0 ≤ h := le_trans (by positivity) hth
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 (by linarith)
  set A : ℝ := c * h * m ^ (-(1 : ℝ) / 2) with hA
  have hmpow : m ^ (-(1 : ℝ) / 2) = (Real.sqrt m)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by linarith)]
    norm_num
  have hA0 : 0 ≤ A := by rw [hA, hmpow]; positivity
  have hAle : A ≤ h / (8 * Real.sqrt m) := by
    rw [hA, hmpow, div_eq_mul_inv, mul_inv]
    have : 0 ≤ h * (Real.sqrt m)⁻¹ := by positivity
    nlinarith
  obtain ⟨C0, hC0, hdec⟩ : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ γ : UJ L.ε,
      ‖⟪w, L.σ (Pc⁻¹ * umat γ * Pc) w⟫_ℂ‖ ≤ C0 * Real.sqrt (hs (umat γ)) ^ (-A) := by
    refine ⟨Real.sqrt ((2 * D.R.rS + (k0 + 1) + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt m)) *
      Real.exp (h / (8 * Real.sqrt m) / Real.sqrt m), ?_, fun γ => ?_⟩
    rotate_left
    · have key := poly_decay_of_decay_statement D h1 _ L.ε L.lam L.hlam L.Hs _ hDS _ hE h hgapAt hth
        (by rw [hmin]; omega) w hlow (umat γ) (umat_mem γ)
      rw [hmin, hmR] at key
      refine le_trans key ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le
      · exact Real.one_le_sqrt.2 (one_le_hilbert_schmidt_of_mem _ _ (umat_mem γ) ⟨0, by omega⟩)
      · linarith
    · positivity
  have hcls := coefT_Cls hPc hσ hirr (hadm _ L.ε L.lam L.Hs _ hDS) hw0 hf
  refine ⟨Cls_smooth hP hσ w hcls, fun ws _ hws => ?_⟩
  obtain ⟨C, hC⟩ := Cls_bound hP hσ w hA0 hC0 hdec (Cls_rdWord hP hσ w hcls ws hws)
  refine ⟨max C 0 * 2 ^ A, fun g hg => ?_⟩
  have e1 : (∑ i, ∑ j, Complex.normSq (g i j)) = hs g := by
    unfold hs; simp only [Complex.normSq_eq_norm_sq]
  rw [e1]
  have hs1 : 1 ≤ Real.sqrt (hs g) := by
    rw [← hs_unitary_conj Pc g hP.1]
    exact Real.one_le_sqrt.2 (one_le_hilbert_schmidt_of_mem _ _ (cj_mem hP hg) ⟨0, by omega⟩)
  refine le_trans (hC g hg) ?_
  set s := Real.sqrt (hs g) with hs_def
  have p1 : 0 < s ^ A := Real.rpow_pos_of_pos (by linarith) _
  have p2 : 0 < (1 + s) ^ A := Real.rpow_pos_of_pos (by linarith) _
  have e2 : (1 + s) ^ A ≤ 2 ^ A * s ^ A := by
    rw [← Real.mul_rpow (by norm_num) (by linarith)]
    exact Real.rpow_le_rpow (by linarith) (by linarith) hA0
  have e3 : s ^ (-A) ≤ 2 ^ A * (1 + s) ^ (-A) := by
    rw [Real.rpow_neg (by linarith), Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ p2,
      inv_mul_le_iff₀ p1]
    linarith
  calc C * s ^ (-A) ≤ max C 0 * s ^ (-A) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ max C 0 * (2 ^ A * (1 + s) ^ (-A)) := mul_le_mul_of_nonneg_left e3 (le_max_right _ _)
    _ = _ := by ring

end Final

section Left

open Formalism.MainNotions.BridgeLemma Formalism.MainNotions.PlaceDegreeData Formalism.BasicNotions

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {Hm Pc : Matrix (Fin n) (Fin n) ℂ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem UH_exp_mul (hP : IsCay ε Hm Pc) {g X : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH Hm)
    (hX : Xᴴ * Hm + Hm * X = 0) (t : ℝ) : NormedSpace.exp ((t : ℂ) • X) * g ∈ Formalism.QuantumDeterminants.UH Hm := by
  obtain ⟨γ, hγ⟩ := exists_UJ (cj_mem hP hg)
  apply mem_of_cj hP
  rw [cj_mul hP, cj_exp hP, cj_smul, ← hγ, ← umat_expG (cj_lie hP hX) t]
  exact umat_mem (expG ε (cj Pc X) t * γ)

theorem Cls_ldM (hP : IsCay ε Hm Pc) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (w : H) {F : Matrix (Fin n) (Fin n) ℂ → V} (hF : Cls Hm Pc hσ w F) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * Hm + Hm * X = 0) : Cls Hm Pc hσ w (ldM X F) := by
  obtain ⟨ι, _, x', x, c, hx', hx, hF⟩ := hF
  have hXJ := cj_lie hP hX
  choose y hy hder using fun i => Vsub_deriv hσ w (hx' i) (inG_neg hXJ)
  refine ⟨ι, inferInstance, y, x, c, hy, hx, fun g hg => ?_⟩
  unfold ldM
  obtain ⟨γ, hγ⟩ := exists_UJ (cj_mem hP hg)
  have e1 : (fun t : ℝ => F (NormedSpace.exp ((t : ℂ) • X) * g)) =
      fun t : ℝ => ∑ i, ⟪σ (NormedSpace.exp ((t : ℂ) • (-cj Pc X))) (x' i), σ (umat γ) (x i)⟫_ℂ • c i := by
    funext t
    rw [hF _ (UH_exp_mul hP hg hX t)]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [cj_mul hP, cj_exp hP, cj_smul, ← hγ, ← umat_expG hXJ t, ← umat_expG (inG_neg hXJ) t]
    have h2 : umat (expG ε (cj Pc X) t) * umat γ = umat (expG ε (cj Pc X) t * γ) := rfl
    rw [h2, rep_mul hσ, rep_inner_left hσ (expG ε (-cj Pc X) t), expG_neg_inv hXJ]
  rw [e1]
  have hd : HasDerivAt (fun t : ℝ => ∑ i, ⟪σ (NormedSpace.exp ((t : ℂ) • (-cj Pc X))) (x' i), σ (umat γ) (x i)⟫_ℂ • c i)
      (∑ i, ⟪y i, σ (umat γ) (x i)⟫_ℂ • c i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    have h3 := HasDerivAt.inner ℂ (hder i) (hasDerivAt_const (0 : ℝ) (σ (umat γ) (x i)))
    simp only [inner_zero_right, zero_add] at h3
    exact h3.smul_const (c i)
  rw [hd.deriv, ← hγ]

theorem Cls_ldWord (hP : IsCay ε Hm Pc) {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (w : H) {F : Matrix (Fin n) (Fin n) ℂ → V} (hF : Cls Hm Pc hσ w F) :
    ∀ ws : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ ws, Xᴴ * Hm + Hm * X = 0) → Cls Hm Pc hσ w (ldWord ws F)
  | [], _ => hF
  | X :: ws, h => Cls_ldM hP hσ w (Cls_ldWord hP hσ w hF ws fun Y hY => h Y (List.mem_cons_of_mem _ hY))
      (h X List.mem_cons_self)

theorem isCay_one (ε : Fin n → Bool) : IsCay ε (Jm ε) 1 := ⟨one_mem _, by simp⟩

theorem kfin_decay_UJ {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) (hadm : AdmProjAt ε σ) {w : H} (hw : w ≠ 0)
    {A C0 : ℝ} (hA : 0 ≤ A) (hC0 : 0 ≤ C0)
    (hdec : ∀ g : UJ ε, ‖⟪w, σ (umat g) w⟫_ℂ‖ ≤ C0 * Real.sqrt (hs (umat g)) ^ (-A))
    {x x' : H} (hx : IsKFin ε σ x) (hx' : IsKFin ε σ x')
    (ws ws' : List (Matrix (Fin n) (Fin n) ℂ)) (hws : ∀ X ∈ ws, inG ε X) (hws' : ∀ X ∈ ws', inG ε X) :
    ∃ Cf : ℝ, ∀ g, inUJ ε g → ‖ldWord ws' (rdWord ws (fun y => ⟪x', σ y x⟫_ℂ)) g‖ ≤ Cf * Real.sqrt (hs g) ^ (-A) := by
  have h0 : Cls (Jm ε) 1 hσ w (fun y => ⟪x', σ y x⟫_ℂ) := by
    refine ⟨Unit, inferInstance, fun _ => x', fun _ => x, fun _ => 1,
      fun _ => kfin_mem_Vsub hσ hirr hadm hw hx', fun _ => kfin_mem_Vsub hσ hirr hadm hw hx, fun g _ => ?_⟩
    simp [cj]
  exact Cls_bound (isCay_one ε) hσ w hA hC0 hdec
    (Cls_ldWord (isCay_one ε) hσ w (Cls_rdWord (isCay_one ε) hσ w h0 ws hws) ws' hws')

end Left

section PK

open Formalism.MainNotions.BridgeLemma Formalism.MainNotions.PlaceDegreeData Formalism.BasicNotions

theorem decay_K_finite_coefficients (D : D7) {c0 : ℝ} (hc0 : 0 ≤ c0) (hc8 : c0 ≤ 1 / 8)
    (ha2 : PlaceDegreeData.adm2 D) (h1 : PlaceDegreeData.DiscreteSeriesDecayBound D) (hadm : HCAdmDS) : CayleySignature.adm3 D c0 := by
  intro k r z c u v b hSet H _ _ _ σ P hP hDS x x' hx hx' ws ws' hws hws' h hlow
  obtain ⟨hk1, _, _, _, _, _, hlam, _, _, t, _, ht, _, hgapT⟩ := hSet
  have hσ : IsURepOn (UJset (CayleySignature.eps48 k r)) (fun g => σ (P⁻¹ * g * P)) := hDS.2.2.1
  have hirr : IsIrredOn (UJset (CayleySignature.eps48 k r)) (fun g => σ (P⁻¹ * g * P)) := hDS.2.2.2.1
  obtain ⟨w, hw⟩ := exists_highest_weight_unit _ _ _ hDS
  have hw0 : w ≠ 0 := by
    intro h0
    have := hw.1
    rw [h0, norm_zero] at this
    norm_num at this
  have hlowU : IsLowUnit (CayleySignature.eps48 k r) (CayleySignature.lam48 k r v b) (fun g => σ (P⁻¹ * g * P)) w := ⟨hw.1, hw.2.1⟩
  have : FiniteDimensional ℂ (lowKSub (CayleySignature.eps48 k r) (CayleySignature.lam48 k r v b) (fun g => σ (P⁻¹ * g * P))) :=
    (ha2 _ _ _ hlam H _ hDS).1.1
  have hE := star_projection_is_orth_proj (lowKSub (CayleySignature.eps48 k r) (CayleySignature.lam48 k r v b) (fun g => σ (P⁻¹ * g * P)))
  obtain ⟨hp, hq⟩ := sig_of_cayley k r _ P hP
  have hmin : min (pOf (CayleySignature.eps48 k r)) (qOf (CayleySignature.eps48 k r)) = r + 1 := by rw [hp, hq]; omega
  set T0 : ℝ := 2 * ((CayleySignature.rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 with hT0
  set hh : ℝ := max h T0 with hhh
  have hlow' : CayleySignature.LowGapGe hh r b := fun j hj => max_le (hlow j hj) (hgapT j hj).le
  have hgapAt := gap_at_least_of_low_gap k r v b hh hk1 hlam.1 hlow'
  have hth0 : 120 * ((2 * r + k + 1 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ T0 := by
    set a : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with ha
    set q : ℝ := ((r + 1 : ℕ) : ℝ) with hq'
    have ha0 : 0 ≤ a := Nat.cast_nonneg _
    have hq1 : 1 ≤ q := by rw [hq']; exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
    have htt : a + 5 ≤ (t : ℝ) := by
      have : 2 * r + k + 1 + 5 ≤ t := ht
      rw [ha]; exact_mod_cast this
    have hM : ((CayleySignature.rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) = a + 2 * q * t := by
      rw [ha, hq']; unfold CayleySignature.rk48; push_cast; ring
    have e1 : q ^ ((3 : ℝ) / 2) ≤ q ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num)
    have e2 : 2 * q * (a + 5) ≤ a + 2 * q * t := by nlinarith
    have e3 : (2 * q * (a + 5)) ^ 3 ≤ (a + 2 * q * t) ^ 3 := pow_le_pow_left₀ (by positivity) e2 3
    have e4 : 75 * a ≤ (a + 5) ^ 3 := by nlinarith [sq_nonneg a, mul_nonneg ha0 (sq_nonneg a)]
    have e5 : q ^ 2 ≤ q ^ 3 := by nlinarith [sq_nonneg q]
    have e6 : 120 * a * q ^ 2 ≤ 2 * (2 * q * (a + 5)) ^ 3 := by
      have : (2 * q * (a + 5)) ^ 3 = 8 * q ^ 3 * (a + 5) ^ 3 := by ring
      rw [this]
      have h7 : q ^ 2 * (75 * a) ≤ q ^ 3 * (a + 5) ^ 3 := mul_le_mul e5 e4 (by positivity) (by positivity)
      nlinarith [mul_nonneg ha0 (sq_nonneg q)]
    rw [hT0, hM]
    have h8 : 120 * a * q ^ ((3 : ℝ) / 2) ≤ 120 * a * q ^ 2 := mul_le_mul_of_nonneg_left e1 (by positivity)
    have h9 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    linarith
  have hth : 120 * ((2 * r + k + 1 : ℕ) : ℝ) *
      ((min (pOf (CayleySignature.eps48 k r)) (qOf (CayleySignature.eps48 k r)) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ hh := by
    rw [hmin]; exact le_trans hth0 (le_max_right _ _)
  have hh0 : 0 ≤ hh := le_trans (by positivity) hth
  have hsq : (2 : ℝ) * ((r + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + 2 := by push_cast; ring
  set sm : ℝ := Real.sqrt (2 * (r : ℝ) + 2) with hsm
  have hsm0 : 0 < sm := Real.sqrt_pos.2 (by positivity)
  set A : ℝ := hh / (8 * sm) with hA
  have hA0 : 0 ≤ A := by positivity
  have hAle : c0 * h / sm ≤ A := by
    rw [hA, div_le_div_iff₀ hsm0 (by positivity)]
    have e1 : c0 * h ≤ hh / 8 := by
      have : c0 * h ≤ c0 * hh := mul_le_mul_of_nonneg_left (le_max_left _ _) hc0
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right e1 hsm0.le]
  have hdec : ∀ γ : UJ (CayleySignature.eps48 k r), ‖⟪w, σ (P⁻¹ * umat γ * P) w⟫_ℂ‖ ≤
      (Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ A * Real.exp (A / sm)) * Real.sqrt (hs (umat γ)) ^ (-A) := by
    intro γ
    have key := poly_decay_of_decay_statement D h1 _ _ _ hlam H _ hDS _ hE hh hgapAt hth
      (by rw [hmin]; omega) w hlowU (umat γ) (umat_mem γ)
    rw [hmin, hsq] at key
    exact key
  obtain ⟨Cf, hCf⟩ := kfin_decay_UJ hσ hirr (hadm _ _ _ H _ hDS) hw0 hA0 (by positivity) hdec hx hx' ws ws' hws hws'
  refine ⟨max Cf 0, fun g hg => ?_⟩
  refine le_trans (hCf g hg) ?_
  have hs1 : 1 ≤ Real.sqrt (hs g) := Real.one_le_sqrt.2 (one_le_hilbert_schmidt_of_mem _ _ hg ⟨0, by omega⟩)
  calc Cf * Real.sqrt (hs g) ^ (-A) ≤ max Cf 0 * Real.sqrt (hs g) ^ (-A) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ max Cf 0 * Real.sqrt (hs g) ^ (-(c0 * h / sm)) := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        exact Real.rpow_le_rpow_of_exponent_le hs1 (by linarith)

theorem pK_of {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {c0 : ℝ} (hc0 : 0 < c0) (hc8 : c0 ≤ 1 / 8)
    (h2 : PlaceDegreeData.admF2 Fm) (h1 : PlaceDegreeData.FamilyDiscreteSeriesDecay Fm) (hadm : HCAdmDS) : PX.KFinDecayF Fm c0 :=
  ⟨hc0, fun x i => decay_K_finite_coefficients (Fm.D x i) hc0.le hc8 (h2 x i) (h1 x i) hadm⟩

theorem pd_of {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {cD C₁ : ℝ} (hc : 0 < cD) (hc8 : cD ≤ 1 / 8) (hC1 : 120 ≤ C₁)
    (h2 : PlaceDegreeData.admF2 Fm) (h1 : PlaceDegreeData.FamilyDiscreteSeriesDecay Fm) (hadm : HCAdmDS) : ∀ x (i : Fm.Ix x), PX.decay (Fm.D x i) cD C₁ :=
  fun x i => stDecay_of (Fm.D x i) hc hc8 hC1 (h2 x i) (h1 x i) hadm

end PK

def eqImg {K H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : K → H →L[ℂ] H) (S : Submodule ℂ H) :
    Submodule ℂ H :=
  sSup {S' | ∃ Θ : S →ₗ[ℂ] H, (∀ (a : K) (v w : S), (w : H) = ρ a v → Θ w = ρ a (Θ v)) ∧ S' = LinearMap.range Θ}

def CompactProj : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (ρ : K → H →L[ℂ] H), ρ 1 = 1 → (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) → (∀ a v, ‖ρ a v‖ = ‖v‖) →
    (∀ v, Continuous fun a => ρ a v) →
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → (∀ a, ∀ v ∈ S, ρ a v ∈ S) →
    ∃ e : K → ℂ, Continuous e ∧ (∀ x ∈ S, ∫ a, e a • ρ a x ∂μ = x) ∧ ∀ v, ∫ a, e a • ρ a v ∂μ ∈ eqImg ρ S

section CPproof

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K] [MeasurableSpace K]
  [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (ρ : K → H →L[ℂ] H)

theorem cp_int {V : Type*} [NormedAddCommGroup V] {f : K → V} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

variable {ρ}

theorem integrable_coefficient_smul (hc : ∀ v, Continuous fun a => ρ a v) (x v y : H) :
    Integrable (fun a => ⟪ρ a x, y⟫_ℂ • ρ a v) μ :=
  cp_int μ (((hc x).inner continuous_const).smul (hc v))

def cpTheta (hc : ∀ v, Continuous fun a => ρ a v) (S : Submodule ℂ H) (x v : H) : S →ₗ[ℂ] H where
  toFun y := ∫ a, ⟪ρ a x, (y : H)⟫_ℂ • ρ a v ∂μ
  map_add' y y' := by
    rw [← integral_add (integrable_coefficient_smul μ hc x v y) (integrable_coefficient_smul μ hc x v y')]
    congr 1; funext a
    simp [add_smul]
  map_smul' c y := by
    simp only [RingHom.id_apply]
    rw [← integral_smul]
    congr 1; funext a
    simp [smul_smul]

theorem cpTheta_mem (hm : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (hi : ∀ a v, ‖ρ a v‖ = ‖v‖)
    (hc : ∀ v, Continuous fun a => ρ a v) (S : Submodule ℂ H) (x v : H) (y : S) :
    cpTheta μ hc S x v y ∈ eqImg ρ S := by
  have : LinearMap.range (cpTheta μ hc S x v) ≤ eqImg ρ S := by
    apply le_sSup
    refine ⟨cpTheta μ hc S x v, ?_, rfl⟩
    intro g y w hw
    show ∫ a, ⟪ρ a x, (w : H)⟫_ℂ • ρ a v ∂μ = ρ g (∫ a, ⟪ρ a x, (y : H)⟫_ℂ • ρ a v ∂μ)
    rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_coefficient_smul μ hc x v y)]
    rw [← integral_mul_left_eq_self (fun a => ⟪ρ a x, (w : H)⟫_ℂ • ρ a v) g]
    congr 1; funext a
    rw [map_smul, hw, hm g a]
    congr 1
    show ⟪ρ g (ρ a x), ρ g y⟫_ℂ = _
    let L : H →ₗᵢ[ℂ] H := ⟨(ρ g : H →ₗ[ℂ] H), fun x => hi _ x⟩
    exact L.inner_map_map _ _
  exact this ⟨y, rfl⟩

theorem compactProj : CompactProj := by
  intro K _ _ _ _ _ _ _ μ _ H _ _ _ ρ h1 hm hi hc S hfd hst
  classical
  set d := Module.finrank ℂ S with hd
  let b : OrthonormalBasis (Fin d) ℂ S := stdOrthonormalBasis ℂ S
  let ι := Fin d × Fin d

  let m : ι → K → ℂ := fun q a => ⟪(b q.1 : H), ρ a (b q.2)⟫_ℂ
  have hmc : ∀ q, Continuous (m q) := fun q => continuous_const.inner (hc _)
  let ee : (ι → ℂ) → K → ℂ := fun c a => ∑ q, c q * star (m q a)
  have hec : ∀ c, Continuous (ee c) := fun c =>
    continuous_finsetSum _ fun q _ => continuous_const.mul (continuous_star.comp (hmc q))
  have hI1 : ∀ c q', Integrable (fun a => ee c a * m q' a) μ := fun c q' => cp_int μ ((hec c).mul (hmc q'))
  let Λ : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun c q' => ∫ a, ee c a * m q' a ∂μ
      map_add' := fun c c' => by
        funext q'
        show ∫ a, ee (c + c') a * m q' a ∂μ = ∫ a, ee c a * m q' a ∂μ + ∫ a, ee c' a * m q' a ∂μ
        rw [← integral_add (hI1 c q') (hI1 c' q')]
        congr 1; funext a
        simp only [ee, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun t c => by
        funext q'
        show ∫ a, ee (t • c) a * m q' a ∂μ = t • ∫ a, ee c a * m q' a ∂μ
        rw [← integral_smul]
        congr 1; funext a
        simp only [ee, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun q _ => by ring }
  let δ : ι → ℂ := fun q => if q.1 = q.2 then 1 else 0
  have hδ : δ ∈ LinearMap.range Λ := by
    by_contra hne
    obtain ⟨φ, hφ, hker⟩ := Submodule.exists_le_ker_of_notMem hne
    let y : ι → ℂ := fun q => φ (fun j => if q = j then 1 else 0)
    have hφe : ∀ X : ι → ℂ, φ X = ∑ q, X q * y q := fun X => by
      rw [LinearMap.pi_apply_eq_sum_univ φ X]
      simp [y]
    let f : K → ℂ := fun a => ∑ q, m q a * y q
    have hfc : Continuous f := continuous_finsetSum _ fun q _ => (hmc q).mul continuous_const
    have h0 : ∫ a, star (f a) * f a ∂μ = 0 := by
      have h2 : φ (Λ (fun q => star (y q))) = 0 := hker ⟨_, rfl⟩
      rw [hφe] at h2
      rw [← h2]
      have h3 : ∀ q' : ι, Λ (fun q => star (y q)) q' * y q' = ∫ a, star (f a) * (m q' a * y q') ∂μ := by
        intro q'
        show (∫ a, ee (fun q => star (y q)) a * m q' a ∂μ) * y q' = _
        rw [← integral_mul_const]
        congr 1; funext a
        have : ee (fun q => star (y q)) a = star (f a) := by
          simp only [ee, f, star_sum, star_mul']
          refine Finset.sum_congr rfl fun q _ => by ring
        rw [this]; ring
      simp_rw [h3]
      have hI2 : ∀ q' : ι, Integrable (fun a => star (f a) * (m q' a * y q')) μ := fun q' =>
        cp_int μ ((continuous_star.comp hfc).mul ((hmc q').mul continuous_const))
      rw [← integral_finsetSum _ fun q' _ => hI2 q']
      congr 1; funext a
      rw [← Finset.mul_sum]
    have h4 : ∀ a, f a = 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨a0, ha0⟩ := hcon
      have hpos : 0 < ∫ a, ‖f a‖ ^ 2 ∂μ := by
        apply Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := a0)
        · exact hfc.norm.pow 2
        · exact HasCompactSupport.of_compactSpace _
        · intro a; positivity
        · positivity
      have h5 : (∫ a, star (f a) * f a ∂μ) = ((∫ a, ‖f a‖ ^ 2 ∂μ : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        congr 1; funext a
        rw [Complex.star_def, Complex.conj_mul']
        push_cast; rfl
      rw [h5] at h0
      have : (∫ a, ‖f a‖ ^ 2 ∂μ) = 0 := by exact_mod_cast h0
      linarith
    apply hφ
    rw [hφe]
    have h6 := h4 1
    have h7 : ∀ q : ι, m q 1 = δ q := by
      intro q
      show ⟪(b q.1 : H), ρ 1 (b q.2)⟫_ℂ = _
      rw [h1]
      have := orthonormal_iff_ite.1 b.orthonormal q.1 q.2
      simpa [δ] using this
    simp only [f, h7] at h6
    exact h6
  obtain ⟨c, hc'⟩ := hδ
  have hIv : ∀ v : H, Integrable (fun a => ee c a • ρ a v) μ := fun v => cp_int μ ((hec c).smul (hc v))
  refine ⟨ee c, hec c, ?_, ?_⟩
  ·
    have hb : ∀ l : Fin d, ∫ a, ee c a • ρ a (b l : H) ∂μ = (b l : H) := by
      intro l
      have e1 : ∀ a, ρ a (b l : H) = ∑ p, m (p, l) a • (b p : H) := by
        intro a
        have h2 := b.sum_repr' ⟨ρ a (b l : H), hst a _ (b l).2⟩
        have h3 := congrArg (fun s : S => (s : H)) h2
        simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
        rw [← h3]
        rfl
      have e2 : ∀ a, ee c a • ρ a (b l : H) = ∑ p, (ee c a * m (p, l) a) • (b p : H) := by
        intro a
        rw [e1 a, Finset.smul_sum]
        refine Finset.sum_congr rfl fun p _ => by rw [smul_smul]
      simp_rw [e2]
      rw [integral_finsetSum _ fun p _ => (hI1 c (p, l)).smul_const _]
      have e3 : ∀ p, ∫ a, (ee c a * m (p, l) a) • (b p : H) ∂μ = δ (p, l) • (b p : H) := by
        intro p
        rw [integral_smul_const]
        congr 1
        exact congrFun hc' (p, l)
      simp_rw [e3]
      simp [δ]
    intro x hx
    have h2 := b.sum_repr' ⟨x, hx⟩
    have h3 := congrArg (fun s : S => (s : H)) h2
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h3
    set t : Fin d → ℂ := fun l => ⟪b l, (⟨x, hx⟩ : S)⟫_ℂ with ht
    have e4 : ∀ a, ee c a • ρ a x = ∑ l, t l • (ee c a • ρ a (b l : H)) := by
      intro a
      conv_lhs => rw [← h3]
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => by rw [map_smul, smul_comm]
    simp_rw [e4]
    have hI3 : ∀ l : Fin d, Integrable (fun a => t l • ee c a • ρ a (b l : H)) μ := fun l => (hIv _).smul (t l)
    rw [integral_finsetSum _ fun l _ => hI3 l]
    simp_rw [integral_smul, hb]
    exact h3
  · intro v
    have e5 : ∫ a, ee c a • ρ a v ∂μ = ∑ q : ι, c q • cpTheta μ hc S (b q.2 : H) v (b q.1) := by
      have e6 : ∀ a, ee c a • ρ a v = ∑ q : ι, c q • (⟪ρ a (b q.2 : H), (b q.1 : H)⟫_ℂ • ρ a v) := by
        intro a
        simp only [ee, Finset.sum_smul]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [smul_smul]
        congr 2
        show star ⟪(b q.1 : H), ρ a (b q.2)⟫_ℂ = _
        rw [Complex.star_def, inner_conj_symm]
      simp_rw [e6]
      have hI4 : ∀ q : ι, Integrable (fun a => c q • (⟪ρ a (b q.2 : H), (b q.1 : H)⟫_ℂ • ρ a v)) μ :=
        fun q => (integrable_coefficient_smul μ hc _ v _).smul (c q)
      rw [integral_finsetSum _ fun q _ => hI4 q]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_smul]
      rfl
    rw [e5]
    exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (cpTheta_mem μ hm hi hc S _ v _)

end CPproof

section HC

def HCMult : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S →
      FiniteDimensional ℂ (eqImg (fun k : KG ε => σ (toMK k)) S)

theorem HCAdm_of (h : HCMult) (hc : CompactProj) : HCAdm := by
  intro n ε H _ _ _ σ hσ hirr x hx
  obtain ⟨S, hfd, hxS, hst⟩ := hx
  obtain ⟨e, he, hfix, hrange⟩ := hc (KG ε) (muK ε) H (fun k : KG ε => σ (toMK k)) hσ.1.1
    (fun a b => hσ.1.2 _ (umat_mem (a : UJ ε)) _ (umat_mem (b : UJ ε)))
    (fun a v => hσ.2.1 _ (umat_mem (a : UJ ε)) v)
    (fun v => (cont_orbit hσ v).comp continuous_subtype_val) S hfd (fun a v hv => hst _ a.2 v hv)
  exact ⟨e, _, he, h n ε H σ hσ hirr S hfd hst, hrange, hfix x hxS⟩

def HCMultDS : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStableOn ε σ S →
      FiniteDimensional ℂ (eqImg (fun k : KG ε => σ (toMK k)) S)

theorem HCMultDS_of_HCMult (h : HCMult) : HCMultDS :=
  fun n ε _ H _ _ _ σ hDS => h n ε H σ hDS.2.2.1 hDS.2.2.2.1

theorem HCAdmDS_of (h : HCMultDS) (hc : CompactProj) : HCAdmDS := by
  intro n ε lam H _ _ _ σ hDS x hx
  have hσ : IsURepOn (UJset ε) σ := hDS.2.2.1
  obtain ⟨S, hfd, hxS, hst⟩ := hx
  obtain ⟨e, he, hfix, hrange⟩ := hc (KG ε) (muK ε) H (fun k : KG ε => σ (toMK k)) hσ.1.1
    (fun a b => hσ.1.2 _ (umat_mem (a : UJ ε)) _ (umat_mem (b : UJ ε)))
    (fun a v => hσ.2.1 _ (umat_mem (a : UJ ε)) v)
    (fun v => (cont_orbit hσ v).comp continuous_subtype_val) S hfd (fun a v hv => hst _ a.2 v hv)
  exact ⟨e, _, he, h n ε lam H σ hDS S hfd hst, hrange, hfix x hxS⟩

end HC

section FromMult

open Formalism.MainNotions.PlaceDegreeData

theorem HCAdm_of_mult (h : HCMult) : HCAdm := HCAdm_of h compactProj

theorem HCAdmDS_of_mult (h : HCMultDS) : HCAdmDS := HCAdmDS_of h compactProj

theorem pd_of_mult {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {cD C₁ : ℝ} (hc : 0 < cD) (hc8 : cD ≤ 1 / 8) (hC1 : 120 ≤ C₁)
    (h2 : PlaceDegreeData.admF2 Fm) (h1 : PlaceDegreeData.FamilyDiscreteSeriesDecay Fm) (h : HCMultDS) : ∀ x (i : Fm.Ix x), PX.decay (Fm.D x i) cD C₁ :=
  pd_of Fm hc hc8 hC1 h2 h1 (HCAdmDS_of_mult h)

theorem pK_of_mult {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) {c0 : ℝ} (hc0 : 0 < c0) (hc8 : c0 ≤ 1 / 8)
    (h2 : PlaceDegreeData.admF2 Fm) (h1 : PlaceDegreeData.FamilyDiscreteSeriesDecay Fm) (h : HCMultDS) : PX.KFinDecayF Fm c0 :=
  pK_of Fm hc0 hc8 h2 h1 (HCAdmDS_of_mult h)

end FromMult

section SmoothVec

open Formalism.MainNotions.BridgeLemma Formalism.BasicNotions

variable {n : ℕ} {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

attribute [local instance] msM
local instance : BorelSpace (Matrix (Fin n) (Fin n) ℂ) := ⟨rfl⟩
local instance : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
local instance : ProperSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.proper ℝ _

theorem locInt_orbit {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H) :
    LocallyIntegrable (fun m : Matrix (Fin n) (Fin n) ℂ => σ m w) ((muG ε).map (fun y : UJ ε => umat y)) := by
  have hemb : MeasurableEmbedding (fun y : UJ ε => umat y) := (isClosedEmbeddingMatrix n ε).1.measurableEmbedding
  rw [locallyIntegrable_iff]
  intro k hk
  rw [hemb.integrableOn_map_iff]
  exact (cont_orbit hσ w).continuousOn.integrableOn_compact ((isClosedEmbeddingMatrix n ε).1.isCompact_preimage hk)

variable [CompleteSpace H]

theorem smooth_vec {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H)
    {Φ : Matrix (Fin n) (Fin n) ℂ → ℂ} (hΦ : IsTest Φ) :
    Formalism.QuantumDeterminants.SmoothOnH (Jm ε) (fun g => σ g (vec ε σ w Φ)) := by
  intro g₀ _
  let 𝒦 : Set (Matrix (Fin n) (Fin n) ℂ) :=
    (fun p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ => p.1 * p.2) ''
      (Metric.closedBall g₀ 1 ×ˢ tsupport Φ)
  have h𝒦 : IsCompact 𝒦 :=
    ((isCompact_closedBall g₀ 1).prod hΦ.2.isCompact).image (continuous_fst.matrix_mul continuous_snd)
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 < R ∧ 𝒦 ⊆ Metric.closedBall 0 R := by
    obtain ⟨R, hR⟩ := h𝒦.isBounded.subset_closedBall 0
    exact ⟨max R 1, by positivity, hR.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))⟩
  let χ : ContDiffBump (0 : Matrix (Fin n) (Fin n) ℂ) := ⟨R, R + 1, hR0, by linarith⟩
  let Ψ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ → ℂ := fun p y => (χ y : ℂ) * Φ (sharpL ε p * y)
  have hΨ : ContDiff ℝ ∞ (Function.uncurry Ψ) := by
    apply ContDiff.mul
    · exact Complex.ofRealCLM.contDiff.comp (χ.contDiff.comp contDiff_snd)
    · exact hΦ.1.comp (ContDiff.mmul ((sharpL ε).contDiff.comp contDiff_fst) contDiff_snd)
  have key := contDiff_param_integral (hB := (⟨rfl⟩ : @BorelSpace _ _ (msM n))) (locInt_orbit hσ w) (Ψ := Ψ)
    (k := tsupport χ) χ.hasCompactSupport.isCompact
    (fun p x hx => by
      have : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [Ψ, this]) hΨ
  refine ⟨Metric.ball g₀ 1, _, Metric.isOpen_ball, Metric.mem_ball_self one_pos, key.contDiffOn, ?_⟩
  intro g hg hgU
  obtain ⟨γ, rfl⟩ := exists_UJ (ε := ε) hgU
  show σ (umat γ) (vec ε σ w Φ) = _
  have h1 := rep_vec hσ w hΦ γ⁻¹
  rw [inv_inv] at h1
  rw [h1, (isClosedEmbeddingMatrix n ε).1.integral_map, vec]
  congr 1
  funext y
  show Φ (umat γ⁻¹ * umat y) • _ = ((χ (umat y) : ℂ) * Φ (sharpL ε (umat γ) * umat y)) • _
  rw [umat_inv_eq]
  by_cases h0 : Φ (sharpL ε (umat γ) * umat y) = 0
  · rw [h0]; simp
  · have hy : umat y ∈ 𝒦 := by
      refine ⟨(umat γ, sharpL ε (umat γ) * umat y), ⟨Metric.ball_subset_closedBall hg, subset_tsupport _ h0⟩, ?_⟩
      show umat γ * (sharpL ε (umat γ) * umat y) = umat y
      rw [← Matrix.mul_assoc, ← umat_inv_eq]
      have : umat γ * umat γ⁻¹ = umat (γ * γ⁻¹) := rfl
      rw [this, mul_inv_cancel]; exact Matrix.one_mul _
    have : χ (umat y) = 1 := χ.one_of_mem_closedBall (hR hy)
    rw [this]; simp

end SmoothVec

section SmoothVecH

open Formalism.MainNotions.BridgeLemma Formalism.BasicNotions

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kfin_smoothVec (hadm : HCAdmDS) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (hσ : IsDSHpk k r ε lam σ)
    {v : H} (hv : IsKFinHpk (k := k) (r := r) σ v) : v ∈ smoothVecs (k := k) (r := r) σ := by
  obtain ⟨Pc, hPc, hDS⟩ := hσ
  have hP : IsCay ε (Formalism.QuantumDeterminants.Hpk k r) Pc := ⟨hPc.2, hPc.1.2⟩
  have iP : Pc⁻¹ = Pcᴴ := Matrix.inv_eq_left_inv (cay1 hP)
  have hrep : IsURepOn (UJset ε) (fun g => σ (Pc⁻¹ * g * Pc)) := hDS.2.2.1
  have hirr : IsIrredOn (UJset ε) (fun g => σ (Pc⁻¹ * g * Pc)) := hDS.2.2.2.1
  obtain ⟨w, hw⟩ := exists_highest_weight_unit ε lam _ hDS
  have hw0 : w ≠ 0 := by
    intro h0
    have := hw.1
    rw [h0, norm_zero] at this
    norm_num at this
  have kf : IsKFin ε (fun g => σ (Pc⁻¹ * g * Pc)) v := by
    obtain ⟨S, hfd, hyS, hst⟩ := hv
    exact ⟨S, hfd, hyS, fun g hg u hu => hst _ (compact_to_unitary_hermitian _ _ _ Pc g hPc hg) u hu⟩
  obtain ⟨Φ, hΦ, rfl⟩ := kfin_mem_Vsub hrep hirr (hadm _ ε lam H _ hDS) hw0 kf
  intro g₀ hg₀
  obtain ⟨U, G, hU, hmem, hG, hag⟩ := smooth_vec hrep w hΦ (cj Pc g₀) (cj_mem hP hg₀)
  refine ⟨(cjL Pc) ⁻¹' U, fun g => G (cjL Pc g), hU.preimage (cjL Pc).continuous, hmem,
    hG.comp (cjL Pc).contDiff.contDiffOn (fun g hg => hg), fun g hg hgU => ?_⟩
  have h2 := hag (cj Pc g) hg (cj_mem hP hgU)
  show σ g _ = G (cj Pc g)
  rw [← h2]
  show σ g _ = σ (Pc⁻¹ * cj Pc g * Pc) _
  congr 2
  rw [iP]
  unfold cj
  calc g = (Pcᴴ * Pc) * g * (Pcᴴ * Pc) := by rw [cay1 hP]; simp
    _ = Pcᴴ * (Pc * g * Pcᴴ) * Pc := by simp only [Matrix.mul_assoc]

end SmoothVecH

end Formalism.MainNotions.BridgeCPX

end
