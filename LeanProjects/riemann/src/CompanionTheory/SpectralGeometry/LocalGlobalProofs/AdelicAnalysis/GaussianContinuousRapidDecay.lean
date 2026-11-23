import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.BB.GaussReg

theorem exists_lower_sup {n : Type} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℝ, c * ‖x‖ ^ 2 ≤ x ⬝ᵥ (P *ᵥ x) := by
  have hpos : ∀ x : n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (P *ᵥ x) := fun x hx => by
    simpa using hP.dotProduct_mulVec_pos hx
  have hcont : Continuous fun x : n → ℝ => x ⬝ᵥ (P *ᵥ x) := by fun_prop
  obtain ⟨c, hc, hmin⟩ : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Metric.sphere (0 : n → ℝ) 1, c ≤ u ⬝ᵥ (P *ᵥ u) := by
    rcases (Metric.sphere (0 : n → ℝ) 1).eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · obtain ⟨u, hu, hm⟩ := (isCompact_sphere (0 : n → ℝ) 1).exists_isMinOn h hcont.continuousOn
      refine ⟨_, hpos u ?_, fun v hv => hm hv⟩
      rintro rfl
      simp at hu
  refine ⟨c, hc, fun x => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : n → ℝ) 1 := by
    simp [norm_smul, hn]
  have h1 := hmin _ hu
  have h2 : (‖x‖⁻¹ • x) ⬝ᵥ (P *ᵥ (‖x‖⁻¹ • x)) = (‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (P *ᵥ x)) := by
    simp [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, sq, mul_assoc]
  rw [h2] at h1
  have h3 : 0 < ‖x‖ ^ 2 := by positivity
  calc c * ‖x‖ ^ 2 ≤ ((‖x‖⁻¹) ^ 2 * (x ⬝ᵥ (P *ᵥ x))) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 h3.le
    _ = x ⬝ᵥ (P *ᵥ x) := by field_simp

theorem posdef_quadratic_lower_bound_l1 {n : Type} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : n → ℝ, c * (∑ p, |x p|) ^ 2 ≤ x ⬝ᵥ (P *ᵥ x) := by
  obtain ⟨c, hc, h⟩ := exists_lower_sup hP
  set N : ℝ := (Fintype.card n : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨c / (N ^ 2 + 1), by positivity, fun x => (?_ : _ ≤ _).trans (h x)⟩
  have h1 : ∑ p, |x p| ≤ N * ‖x‖ := by
    calc ∑ p, |x p| ≤ ∑ _p : n, ‖x‖ := Finset.sum_le_sum fun p _ => norm_le_pi_norm x p
      _ = N * ‖x‖ := by simp [N]
  have h0 : 0 ≤ ∑ p, |x p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h2 : (∑ p, |x p|) ^ 2 ≤ (N ^ 2 + 1) * ‖x‖ ^ 2 := by
    have := pow_le_pow_left₀ h0 h1 2
    nlinarith [sq_nonneg ‖x‖]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem exists_lower_family {ι n : Type} [Fintype ι] [Fintype n] [DecidableEq n]
    {P : ι → Matrix n n ℝ} (hP : ∀ i, (P i).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ι → n → ℝ,
      c * (∑ i, ∑ p, |y i p|) ^ 2 ≤ ∑ i, y i ⬝ᵥ (P i *ᵥ y i) := by
  choose c hc h using fun i => posdef_quadratic_lower_bound_l1 (hP i)
  obtain ⟨c0, hc0, hle⟩ : ∃ c0 : ℝ, 0 < c0 ∧ ∀ i, c0 ≤ c i := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
    · obtain ⟨i, hi⟩ := Finite.exists_min c
      exact ⟨c i, hc i, hi⟩
  set W : ℝ := (Fintype.card ι : ℝ)
  have hW : 0 ≤ W := Nat.cast_nonneg _
  refine ⟨c0 / (W + 1), by positivity, fun y => ?_⟩
  have h1 : (∑ i, ∑ p, |y i p|) ^ 2 ≤ W * ∑ i, (∑ p, |y i p|) ^ 2 := by
    simpa [W] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ∑ p, |y i p|)
  have hS : 0 ≤ ∑ i, (∑ p, |y i p|) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : c0 * ∑ i, (∑ p, |y i p|) ^ 2 ≤ ∑ i, y i ⬝ᵥ (P i *ᵥ y i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      (mul_le_mul_of_nonneg_right (hle i) (sq_nonneg _)).trans (h i (y i))
  refine le_trans ?_ h2
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have h3 : (∑ i, ∑ p, |y i p|) ^ 2 ≤ (W + 1) * ∑ i, (∑ p, |y i p|) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h3 hc0.le]

theorem exp_mul_pow_le {a : ℝ} (ha : 0 < a) (N : ℕ) {s : ℝ} (hs : 0 ≤ s) {q : ℝ} (hq : a * s ^ 2 ≤ q) :
    Real.exp (-q) * (1 + s) ^ N ≤ Real.exp ((N : ℝ) ^ 2 / (4 * a)) := by
  have h1 : (1 + s) ^ N ≤ Real.exp ((N : ℝ) * s) := by
    rw [mul_comm, Real.exp_mul, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp s]) N
  calc Real.exp (-q) * (1 + s) ^ N ≤ Real.exp (-q) * Real.exp ((N : ℝ) * s) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = Real.exp (-q + (N : ℝ) * s) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.2
      have h2 : (N : ℝ) * s ≤ a * s ^ 2 + (N : ℝ) ^ 2 / (4 * a) := by
        have : 0 ≤ (2 * a * s - N) ^ 2 / (4 * a) := by positivity
        have e : (2 * a * s - N) ^ 2 / (4 * a) = a * s ^ 2 + (N : ℝ) ^ 2 / (4 * a) - N * s := by
          field_simp
          ring
        linarith
      linarith

end GlobalTheory.CompanionTheory.SW.BB.GaussReg

namespace GlobalTheory.CompanionTheory.SW.BB

open GaussReg

theorem sizeTup_eq_sum_xw {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {M d : ℕ} (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ))
    (he : ∀ y w, |e y w| = ‖y w‖) (X : Fin 1 → Fin M → Ainf F ⊗[F] E) :
    sizeTup b X = ∑ w, ∑ p, |xw e b X w p| := by
  simp only [sizeTup, sizeInf, xw, cv, he, Fintype.sum_prod_type, Fin.sum_univ_one]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem gaussQ_continuous_rapidDecay : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ y w, |e y w| = ‖y w‖) → ∀ (Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ), Continuous (gaussQ e b Pm) ∧ ((∀ w, (Pm w).PosDef) → RapidDecay b (fun X => (gaussQ e b Pm X : ℂ))) := by
  intro F E _ _ _ _ _ σ hCM M d b e hom he Pm
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  obtain ⟨-, -, -, -, -, -, hco, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  have hxw : ∀ w p, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w p := by
    intro w p
    have h := (hco d b).continuous
    exact (continuous_apply w).comp (hom.continuous.comp ((continuous_apply p.2).comp
      (h.comp ((continuous_apply p.1).comp (continuous_apply 0)))))
  have hxw' : ∀ w, Continuous fun X : Fin 1 → Fin M → Ainf F ⊗[F] E => xw e b X w := fun w =>
    continuous_pi (hxw w)
  refine ⟨?_, fun hP N => ?_⟩
  · unfold gaussQ
    refine Real.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun w _ => ?_))
    exact (hxw' w).dotProduct (Continuous.matrix_mulVec continuous_const (hxw' w))
  · obtain ⟨c, hc, hlow⟩ := exists_lower_family hP
    refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * (Real.pi * c))), fun X => ?_⟩
    have hs := sizeTup_eq_sum_xw b e he X
    have hs0 : 0 ≤ sizeTup b X := by
      rw [hs]
      exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hq := hlow fun w => xw e b X w
    rw [← hs] at hq
    have hn : ‖((gaussQ e b Pm X : ℝ) : ℂ)‖ = gaussQ e b Pm X := by
      rw [Complex.norm_real, gaussQ, Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [hn]
    have key := exp_mul_pow_le (a := Real.pi * c) (mul_pos Real.pi_pos hc) N hs0
      (q := Real.pi * ∑ w, xw e b X w ⬝ᵥ (Pm w *ᵥ xw e b X w))
      (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hq Real.pi_pos.le)
    simpa [gaussQ, neg_mul] using key

end GlobalTheory.CompanionTheory.SW.BB
