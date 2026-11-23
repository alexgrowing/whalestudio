import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PConstants
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace EffectiveHS

open Finset

structure MulTower (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] where

  W : Submodule R A

  V : ℕ → Submodule R A

  mul_mem : ∀ j, ∀ w ∈ W, ∀ f ∈ V j, w * f ∈ V (j + 1)

def mono {A : Type*} [CommRing A] {D : ℕ} (s : Fin D → A) (α : Fin D → ℕ) : A :=
  ∏ i, s i ^ α i

namespace MulTower

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (τ : MulTower R A)

def Raises (k : ℕ) (x : A) : Prop := ∀ j, ∀ f ∈ τ.V j, x * f ∈ τ.V (j + k)

theorem raises_one : τ.Raises 0 1 := by
  intro j f hf
  simpa using hf

theorem raises_of_mem {w : A} (hw : w ∈ τ.W) : τ.Raises 1 w :=
  fun j f hf => τ.mul_mem j w hw f hf

theorem Raises.mul {τ : MulTower R A} {k l : ℕ} {x y : A} (hx : τ.Raises k x)
    (hy : τ.Raises l y) : τ.Raises (k + l) (x * y) := by
  intro j f hf
  have e : j + (k + l) = j + l + k := by omega
  rw [e, mul_assoc]
  exact hx _ _ (hy j f hf)

theorem Raises.pow {τ : MulTower R A} {k : ℕ} {x : A} (hx : τ.Raises k x) (n : ℕ) :
    τ.Raises (k * n) (x ^ n) := by
  induction n with
  | zero => simpa using τ.raises_one
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact ih.mul hx

theorem raises_prod {ι : Type*} (t : Finset ι) (k : ι → ℕ) (x : ι → A)
    (h : ∀ i ∈ t, τ.Raises (k i) (x i)) : τ.Raises (∑ i ∈ t, k i) (∏ i ∈ t, x i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using τ.raises_one
  | insert a t ha ih =>
    rw [sum_insert ha, prod_insert ha]
    exact (h a (mem_insert_self a t)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

theorem raises_mono {D : ℕ} {s : Fin D → A} (hs : ∀ i, s i ∈ τ.W) (α : Fin D → ℕ) :
    τ.Raises (∑ i, α i) (mono s α) := by
  have h := τ.raises_prod univ (fun i => 1 * α i) (fun i => s i ^ α i)
    (fun i _ => (τ.raises_of_mem (hs i)).pow (α i))
  simpa [mono] using h

theorem raises_prod_alt {k : ℕ} (w : Fin k → A) (hw : ∀ i, w i ∈ τ.W) :
    τ.Raises k (∏ i, w i) := by
  have h := τ.raises_prod univ (fun _ => 1) w (fun i _ => τ.raises_of_mem (hw i))
  simpa using h

def P (D T : ℕ) (s : Fin D → A) : Submodule R A :=
  Submodule.span R {F | ∃ α : Fin D → ℕ, ∃ h ∈ τ.V D, ∑ i, α i = T - D ∧ F = mono s α * h}

def Vpp (D T a₀ : ℕ) (s : Fin D → A) : Submodule R A :=
  Submodule.span R {F | ∃ (α : Fin D → ℕ) (k : ℕ) (w : Fin k → A) (m : A),
      (∀ i, w i ∈ τ.W) ∧ m ∈ τ.V 0 ∧ ∑ i, α i + k = T ∧ ∑ i, α i ≤ a₀ ∧
        F = mono s α * (∏ i, w i) * m} ⊔ τ.P D T s

variable {D : ℕ} {s : Fin D → A}

theorem gen_mem (hs : ∀ i, s i ∈ τ.W) {T : ℕ} (α : Fin D → ℕ) {k : ℕ} (w : Fin k → A)
    (hw : ∀ i, w i ∈ τ.W) {m : A} (hm : m ∈ τ.V 0) (hT : ∑ i, α i + k = T) :
    mono s α * (∏ i, w i) * m ∈ τ.V T := by
  have h := ((τ.raises_mono hs α).mul (τ.raises_prod_alt w hw)) 0 m hm
  rwa [zero_add, hT] at h

theorem gen_mem_Vpp {T a₀ : ℕ} (α : Fin D → ℕ) {k : ℕ} (w : Fin k → A)
    (hw : ∀ i, w i ∈ τ.W) {m : A} (hm : m ∈ τ.V 0) (hT : ∑ i, α i + k = T)
    (ha : ∑ i, α i ≤ a₀) : mono s α * (∏ i, w i) * m ∈ τ.Vpp D T a₀ s :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨α, k, w, m, hw, hm, hT, ha, rfl⟩)

theorem P_le (hs : ∀ i, s i ∈ τ.W) {T : ℕ} (hDT : D ≤ T) : τ.P D T s ≤ τ.V T := by
  rw [P, Submodule.span_le]
  rintro F ⟨α, h, hh, hα, rfl⟩
  have h' := τ.raises_mono hs α D h hh
  rwa [hα, Nat.add_sub_cancel' hDT] at h'

theorem Vpp_le (hs : ∀ i, s i ∈ τ.W) {T a₀ : ℕ} (hDT : D ≤ T) : τ.Vpp D T a₀ s ≤ τ.V T := by
  refine sup_le ?_ (τ.P_le hs hDT)
  rw [Submodule.span_le]
  rintro F ⟨α, k, w, m, hw, hm, hT, -, rfl⟩
  exact τ.gen_mem hs α w hw hm hT

end MulTower

noncomputable def polyTower : MulTower ℚ (MvPolynomial (Fin 2) ℚ) where
  W := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ 1
  V j := MvPolynomial.homogeneousSubmodule (Fin 2) ℚ j
  mul_mem j w hw f hf := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hw hf ⊢
    have h := hw.mul hf
    rwa [add_comm] at h

theorem polyTower_nontrivial :
    MvPolynomial.X 0 ∈ polyTower.W ∧ (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ≠ 0 ∧
      mono (fun i => MvPolynomial.X i) (fun _ => 1) * (∏ i : Fin 0, Fin.elim0 i) * 1 ∈
        polyTower.Vpp 2 2 2 (fun i => MvPolynomial.X i) := by
  refine ⟨?_, MvPolynomial.X_ne_zero 0, ?_⟩
  · show _ ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℚ 1
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_X ℚ 0
  · refine polyTower.gen_mem_Vpp (fun _ => 1) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) ?_
      (by simp) (by simp)
    show (1 : MvPolynomial (Fin 2) ℚ) ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℚ 0
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_one (Fin 2) ℚ

section Lift

open MeasureTheory

theorem lift_normSq_le_of {X ι : Type*} [MeasurableSpace X] (μ : Measure X) [Fintype ι]
    (u Ft : ι → X → ℂ) (r G : ι → ℝ) (K B N : ℝ) (hB : 0 ≤ B)
    (hu : ∀ i x, ‖u i x‖ ≤ r i) (hFt : ∀ i, Integrable (fun x => ‖Ft i x‖ ^ 2) μ)
    (hL : ∀ i, ∫ x, ‖Ft i x‖ ^ 2 ∂μ ≤ K * G i ^ 2)
    (hN : N ^ 2 ≤ B * ∫ x, ‖∑ i, u i x * Ft i x‖ ^ 2 ∂μ) :
    N ^ 2 ≤ B * K * (Fintype.card ι) * ∑ i, r i ^ 2 * G i ^ 2 := by
  have hpt : ∀ x, ‖∑ i, u i x * Ft i x‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, r i ^ 2 * ‖Ft i x‖ ^ 2 := by
    intro x
    have h1 : ‖∑ i, u i x * Ft i x‖ ≤ ∑ i, r i * ‖Ft i x‖ := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun i _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hu i x) (norm_nonneg _)
    have h2 := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := fun i => r i * ‖Ft i x‖)
    calc ‖∑ i, u i x * Ft i x‖ ^ 2 ≤ (∑ i, r i * ‖Ft i x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := by simpa [mul_pow, card_univ] using h2
  have hint : Integrable (fun x => (Fintype.card ι : ℝ) * ∑ i, r i ^ 2 * ‖Ft i x‖ ^ 2) μ :=
    (integrable_finsetSum _ fun i _ => (hFt i).const_mul (r i ^ 2)).const_mul _
  have hI : ∫ x, ‖∑ i, u i x * Ft i x‖ ^ 2 ∂μ ≤
      (Fintype.card ι : ℝ) * ∑ i, r i ^ 2 * (K * G i ^ 2) := by
    calc ∫ x, ‖∑ i, u i x * Ft i x‖ ^ 2 ∂μ
        ≤ ∫ x, (Fintype.card ι : ℝ) * ∑ i, r i ^ 2 * ‖Ft i x‖ ^ 2 ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hint
            (Filter.Eventually.of_forall hpt)
      _ = (Fintype.card ι : ℝ) * ∑ i, r i ^ 2 * ∫ x, ‖Ft i x‖ ^ 2 ∂μ := by
          rw [integral_const_mul, integral_finsetSum _ fun i _ => (hFt i).const_mul (r i ^ 2)]
          simp_rw [integral_const_mul]
      _ ≤ _ := by
          gcongr with i
          exact hL i
  calc N ^ 2 ≤ B * ((Fintype.card ι : ℝ) * ∑ i, r i ^ 2 * (K * G i ^ 2)) :=
        hN.trans (mul_le_mul_of_nonneg_left hI hB)
    _ = B * K * (Fintype.card ι) * ∑ i, r i ^ 2 * G i ^ 2 := by
        rw [mul_sum, mul_sum, mul_sum]
        refine sum_congr rfl fun i _ => ?_
        ring

noncomputable def cD (D : ℕ) : ℝ := 2 ^ (D + 1) * Real.pi ^ D / (D - 1).factorial

theorem cD_pos (D : ℕ) : 0 < cD D := by
  unfold cD
  have := Real.pi_pos
  positivity

theorem cD_le (D : ℕ) : cD D ≤ 2 * (2 * Real.pi) ^ D := by
  unfold cD
  have h1 : (1 : ℝ) ≤ (D - 1).factorial := by exact_mod_cast Nat.factorial_pos (D - 1)
  have h0 : (0 : ℝ) ≤ 2 ^ (D + 1) * Real.pi ^ D := by have := Real.pi_pos; positivity
  calc 2 ^ (D + 1) * Real.pi ^ D / (D - 1).factorial ≤ 2 ^ (D + 1) * Real.pi ^ D :=
        div_le_self h0 h1
    _ = 2 * (2 * Real.pi) ^ D := by rw [mul_pow, pow_succ]; ring

theorem lift_normSq_le {X ι : Type*} [MeasurableSpace X] (μ : Measure X) [Fintype ι]
    (D T : ℕ) (β r : ℝ) (hβ : 0 ≤ β) (u Ft : ι → X → ℂ) (rα G : ι → ℝ) (N : ℝ)
    (hu : ∀ i x, ‖u i x‖ ≤ rα i) (hFt : ∀ i, Integrable (fun x => ‖Ft i x‖ ^ 2) μ)
    (hL : ∀ i, ∫ x, ‖Ft i x‖ ^ 2 ∂μ ≤ 140 * cD D * r ^ (2 * D) * G i ^ 2)
    (hN : N ^ 2 ≤ β ^ (T + D + 1) * ∫ x, ‖∑ i, u i x * Ft i x‖ ^ 2 ∂μ) :
    N ^ 2 ≤ (β ^ (T + D + 1) * 140 * cD D * (Fintype.card ι) * r ^ (2 * D)) *
      ∑ i, rα i ^ 2 * G i ^ 2 := by
  have h := lift_normSq_le_of μ u Ft rα G (140 * cD D * r ^ (2 * D)) (β ^ (T + D + 1)) N
    (by positivity) hu hFt hL hN
  calc N ^ 2 ≤ _ := h
    _ = _ := by ring

theorem lift_level (D T a : ℕ) (hD : 1 ≤ D) (ha : a + D + 1 ≤ T) :
    D + 1 ≤ T - a ∧ 2 ≤ D + 1 := by omega

theorem lift_hyps_inhabited :
    (∀ (i : Fin 1) (x : Unit), ‖(fun _ _ => (1 : ℂ)) i x‖ ≤ (fun _ => (1 : ℝ)) i) ∧
    (∀ i : Fin 1, Integrable (fun x : Unit => ‖(fun _ _ => (1 : ℂ)) i x‖ ^ 2)
      (Measure.dirac ())) ∧
    (∀ i : Fin 1, ∫ x : Unit, ‖(fun _ _ => (1 : ℂ)) i x‖ ^ 2 ∂(Measure.dirac ()) ≤
      (1 : ℝ) * (fun _ => (1 : ℝ)) i ^ 2) ∧
    ((1 : ℝ) ^ 2 ≤ 1 * ∫ x : Unit, ‖∑ i : Fin 1, (fun _ _ => (1 : ℂ)) i x *
      (fun _ _ => (1 : ℂ)) i x‖ ^ 2 ∂(Measure.dirac ())) := by
  refine ⟨fun _ _ => by simp, fun _ => integrable_const _, fun _ => by simp, by simp⟩

end Lift

open Real in

theorem lift_constants_le (D : ℕ) (hD : 1 ≤ D) (ρ ρ₁ T C : ℝ) (hρ : 2 ^ 26 ≤ ρ)
    (hDρ : (D : ℝ) ≤ ρ) (h1 : 1 ≤ ρ₁) (h1ρ : ρ₁ ≤ ρ) (hT : 1 ≤ T) (hC : 26 ≤ C) :
    2 * D * log ρ₁ + D * log (Real.sqrt D * ρ₁) + (1 / 2) * log (140 * cD D * T ^ D) ≤
        4 * D * log (ρ * T) ∧
      4 * D * log (ρ * T) ≤ C * D ^ 2 * log (ρ * T) := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hρ0 : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ
  have hρ₁0 : 0 < ρ₁ := lt_of_lt_of_le one_pos h1
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have hlogT : 0 ≤ log T := log_nonneg hT
  have hlogρ₁ : log ρ₁ ≤ log ρ := log_le_log hρ₁0 h1ρ
  have hlogD : log D ≤ log ρ := log_le_log (by linarith) hDρ
  have hlogD0 : 0 ≤ log (D : ℝ) := log_nonneg hD'
  have hlogρ₁0 : 0 ≤ log ρ₁ := log_nonneg h1
  obtain ⟨hc1, hc2⟩ := half_log_add_le_half_log (D : ℝ) ρ hD' hρ
  have hcD := cD_pos D
  have hcDle : log (cD D) ≤ log 2 + D * log (2 * π) := by
    have h := log_le_log hcD (cD_le D)
    rwa [log_mul (by norm_num) (by positivity), log_pow] at h
  have hsplit : log (140 * cD D * T ^ D) = log 140 + log (cD D) + D * log T := by
    rw [log_mul (by positivity) (by positivity), log_mul (by norm_num) hcD.ne', log_pow]
  have h280 : log 280 = log 140 + log 2 := by
    rw [← log_mul (by norm_num) (by norm_num)]; norm_num
  have hsq : log (Real.sqrt D * ρ₁) = log D / 2 + log ρ₁ := by
    rw [log_mul (by positivity) hρ₁0.ne', log_sqrt (by positivity)]
  have hρT : log (ρ * T) = log ρ + log T := log_mul hρ0.ne' hT0.ne'
  have hlogρ : 0 ≤ log ρ := log_nonneg (by linarith)
  refine ⟨?_, ?_⟩
  · rw [hsplit, hsq, hρT]
    have e1 : (D : ℝ) * log ρ₁ ≤ D * log ρ := mul_le_mul_of_nonneg_left hlogρ₁ (by linarith)
    have e2 : (D : ℝ) * log D ≤ D * log ρ := mul_le_mul_of_nonneg_left hlogD (by linarith)
    have e3 : (D : ℝ) * log T ≥ 0 := mul_nonneg (by linarith) hlogT
    nlinarith
  · rw [hρT]
    have hL : 0 ≤ log ρ + log T := by linarith
    have hDD : 4 * (D : ℝ) ≤ C * D ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hDD hL

end EffectiveHS

end GroundTheory.Heights₂.Heights
