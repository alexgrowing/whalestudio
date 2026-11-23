import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open MeasureTheory Matrix Filter Topology
open GroundTheory.LocalField GroundTheory.Automorphic
open Ad3 Ad3.R
open scoped ValuativeRel ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.RankinSelbergTorusIntegrals

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def pf (ψ : AddChar F Circle) (φ : (Fin 2 → F) → ℂ) (u t : F) : ℂ :=
  ∫ y, φ ![u, y] * (ψ (-(y * t)) : ℂ) ∂selfDualMeasure ψ

theorem whittaker_torus_integral_formula (ψ : AddChar F Circle) (μ₁ μ₂ : Fˣ →* ℂˣ) (φ : (Fin 2 → F) → ℂ) (a : Fˣ) :
    W2 ψ μ₁ μ₂ φ (dg2 a 1) = ((μ₁ a : ℂˣ) : ℂ) * mp a (1 / 2) *
      ∫ u : Fˣ, (((μ₁ u)⁻¹ * μ₂ u : ℂˣ) : ℂ) * pf ψ φ u ((a * u⁻¹ : Fˣ) : F) ∂multHaar F := by
  have hdet : GeneralLinearGroup.det (dg2 a (1 : Fˣ)) = a := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, dg2, Matrix.det_fin_two]
  have hrow : ∀ (h : Fˣ) (x : F), ![(h : F), h * x] ᵥ* ((dg2 a (1 : Fˣ) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = ![((a * h : Fˣ) : F), h * x] := by
    intro h x
    ext i
    fin_cases i <;> simp [dg2, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  have hin : ∀ h : Fˣ, (∫ x, φ (![(h : F), h * x] ᵥ* ((dg2 a (1 : Fˣ) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ)
      = ((modulus (h : F) : ℝ))⁻¹ • pf ψ φ ((a * h : Fˣ) : F) ((h⁻¹ : Fˣ) : F) := by
    intro h
    have := integral_comp_mul_left (selfDualMeasure ψ) h.ne_zero
      (fun y : F => φ ![((a * h : Fˣ) : F), y] * (ψ (-(y * ((h⁻¹ : Fˣ) : F))) : ℂ))
    rw [pf, ← this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hx : (h : F) * x * ((h⁻¹ : Fˣ) : F) = x := by
      rw [mul_comm (h : F) x, mul_assoc, Units.mul_inv, mul_one]
    simp only [hrow, hx]
  set G : Fˣ → ℂ := fun u => (((μ₁ u)⁻¹ * μ₂ u : ℂˣ) : ℂ) * pf ψ φ u ((a * u⁻¹ : Fˣ) : F) with hG
  have hpt : ∀ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      (∫ x, φ (![(h : F), h * x] ᵥ* ((dg2 a (1 : Fˣ) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ)
      = ((((μ₁ a)⁻¹ * μ₂ a)⁻¹ : ℂˣ) : ℂ) * G (a * h) := by
    intro h
    have hm : mp h 1 * (((modulus (h : F) : ℝ))⁻¹ : ℝ) = 1 := by
      have : ((modulus (h : F) : ℝ)) ≠ 0 := by exact_mod_cast modulus_ne_zero h.ne_zero
      simp only [mp, Complex.cpow_one]
      push_cast
      field_simp
    have hu : a * (a * h)⁻¹ = h⁻¹ := by rw [mul_inv, ← mul_assoc, mul_inv_cancel, one_mul]
    have hν : (μ₁ (a * h))⁻¹ * μ₂ (a * h) = ((μ₁ a)⁻¹ * μ₂ a) * ((μ₁ h)⁻¹ * μ₂ h) := by
      rw [map_mul, map_mul, mul_inv, mul_mul_mul_comm]
    have hb : ((((μ₁ a)⁻¹ * μ₂ a)⁻¹ : ℂˣ) : ℂ) * (((μ₁ a)⁻¹ * μ₂ a : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hin, hG]
    simp only [hu, hν, Complex.real_smul, Units.val_mul (((μ₁ a)⁻¹ * μ₂ a)) ((μ₁ h)⁻¹ * μ₂ h)]
    linear_combination (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * pf ψ φ ((a * h : Fˣ) : F) ((h⁻¹ : Fˣ) : F) * (hm - hb)
  rw [W2, hdet]
  simp_rw [hpt]
  rw [integral_const_mul, integral_mul_left_eq_self G a]
  have hμ : μ₂ a * ((μ₁ a)⁻¹ * μ₂ a)⁻¹ = μ₁ a := by
    rw [mul_inv, inv_inv, mul_comm (μ₁ a), mul_inv_cancel_left]
  have hμ' : ((μ₁ a : ℂˣ) : ℂ) = ((μ₂ a : ℂˣ) : ℂ) * ((((μ₁ a)⁻¹ * μ₂ a)⁻¹ : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, hμ]
  rw [hμ']
  ring

theorem exists_inv_sb {φ : (Fin 2 → F) → ℂ} (hφ : SB φ) :
    ∃ N : ℤ, ∀ (u y : F), ∀ l ∈ valBall F N, φ ![u, y + l] = φ ![u, y] := by
  obtain ⟨hlc, hcs⟩ := hφ
  have hc : Continuous fun p : (Fin 2 → F) × F => p.1 + ![0, p.2] := by
    refine continuous_fst.add (continuous_pi fun i => ?_)
    fin_cases i
    · simpa using continuous_const
    · simpa using continuous_snd
  have hopen : IsOpen {p : (Fin 2 → F) × F | φ (p.1 + ![0, p.2]) = φ p.1} := by
    have h1 := (hlc.comp_continuous hc).sub (hlc.comp_continuous continuous_fst)
    have := h1.isOpen_fiber 0
    convert this using 1
    ext p
    simp [sub_eq_zero]
  obtain ⟨U, V, -, hV, hsU, h0V, hUV⟩ := generalized_tube_lemma hcs.isCompact
    (isCompact_singleton (x := (0 : F))) hopen (by
      rintro ⟨r, l⟩ ⟨-, hl⟩
      have : l = 0 := hl
      subst this
      have : ![(0 : F), 0] = 0 := by ext i; fin_cases i <;> rfl
      change φ (r + ![0, 0]) = φ r
      rw [this, add_zero])
  obtain ⟨N, -, hN⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp (hV.mem_nhds (h0V rfl))
  have hval : ∀ r ∈ tsupport φ, ∀ l ∈ valBall F N, φ (r + ![0, l]) = φ r := fun r hr l hl =>
    hUV (Set.mk_mem_prod (hsU hr) (hN hl))
  refine ⟨N, fun u y l hl => ?_⟩
  have e : ![u, y + l] = ![u, y] + ![0, l] := by
    ext i; fin_cases i <;> simp
  rw [e]
  by_cases h1 : ![u, y] ∈ tsupport φ
  · exact hval _ h1 l hl
  by_cases h2 : ![u, y] + ![0, l] ∈ tsupport φ
  · have := hval _ h2 (-l) (neg_mem hl)
    have e2 : ![u, y] + ![0, l] + ![0, -l] = ![u, y] := by
      ext i; fin_cases i <;> simp
    rw [e2] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

theorem exists_supp_sb {φ : (Fin 2 → F) → ℂ} (hφ : SB φ) :
    ∃ M : ℤ, ∀ r, φ r ≠ 0 → r 0 ∈ valBall F M ∧ r 1 ∈ valBall F M := by
  have key : ∀ i : Fin 2, ∃ m : ℕ, (fun r : Fin 2 → F => r i) '' tsupport φ ⊆ (valBall F (-(m : ℤ)) : Set F) := by
    intro i
    refine (hφ.2.isCompact.image (continuous_apply i)).elim_directed_cover
      (fun m : ℕ => (valBall F (-(m : ℤ)) : Set F)) (fun m => isOpen_valBall _) ?_ ?_
    · intro x _
      simp only [Set.mem_iUnion]
      exact exists_mem_valBall_neg_nat x
    · exact Monotone.directed_le fun a b hab => valBall_antitone (by omega)
  obtain ⟨m₀, h₀⟩ := key 0
  obtain ⟨m₁, h₁⟩ := key 1
  refine ⟨-(max m₀ m₁ : ℕ), fun r hr => ?_⟩
  have hs := subset_tsupport φ hr
  exact ⟨valBall_antitone (by simp) (h₀ ⟨r, hs, rfl⟩), valBall_antitone (by simp) (h₁ ⟨r, hs, rfl⟩)⟩

theorem pf_eq_zero_of_u {ψ : AddChar F Circle} {φ : (Fin 2 → F) → ℂ} {M : ℤ}
    (hM : ∀ r, φ r ≠ 0 → r 0 ∈ valBall F M ∧ r 1 ∈ valBall F M) {u : F} (hu : u ∉ valBall F M) (t : F) :
    pf ψ φ u t = 0 := by
  have : ∀ y, φ ![u, y] = 0 := fun y => by
    by_contra h
    exact hu (by simpa using (hM _ h).1)
  simp [pf, this]

theorem partial_fourier_eventually_zero {ψ : AddChar F Circle} (hψ1 : ψ ≠ 1) {φ : (Fin 2 → F) → ℂ} {N : ℤ}
    (hN : ∀ (u y : F), ∀ l ∈ valBall F N, φ ![u, y + l] = φ ![u, y]) :
    ∃ M : ℤ, ∀ (u t : F), t ∉ valBall F M → pf ψ φ u t = 0 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra h
    push Not at h
    exact hψ1 (by ext x; simp [h x])
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one ψ)
  refine ⟨ord x₀ - N, fun u t ht => ?_⟩
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (zero_mem _)
  have hl : -(x₀ / t) ∈ valBall F N := by
    refine neg_mem ?_
    rw [mem_valBall_iff_le_ord (div_ne_zero hx₀0 ht0)]
    rw [mem_valBall_iff_le_ord ht0] at ht
    have : ord x₀ = ord (x₀ / t) + ord t := by
      rw [← ord_mul (div_ne_zero hx₀0 ht0) ht0, div_mul_cancel₀ _ ht0]
    omega
  have hshift : pf ψ φ u t = (ψ x₀ : ℂ) * pf ψ φ u t := by
    rw [pf, ← integral_const_mul]
    rw [← integral_add_right_eq_self (μ := selfDualMeasure ψ)
      (fun y => φ ![u, y] * (ψ (-(y * t)) : ℂ)) (-(x₀ / t))]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have e : -((y + -(x₀ / t)) * t) = x₀ + -(y * t) := by
      field_simp
      ring
    simp only [hN u y _ hl, e, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  exact eq_zero_of_eq_mul_of_ne_one (fun h => hx₀ (Circle.ext (by simpa using h))) hshift

theorem continuous_pf {ψ : AddChar F Circle} (hψ : Continuous ψ) {φ : (Fin 2 → F) → ℂ} (hφ : SB φ) :
    Continuous fun p : F × F => pf ψ φ p.1 p.2 := by
  obtain ⟨M, hM⟩ := exists_supp_sb hφ
  have hφc : Continuous φ := hφ.1.continuous
  have hrow : Continuous fun q : (F × F) × F => (![q.1.1, q.2] : Fin 2 → F) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using (continuous_fst.fst : Continuous fun q : (F × F) × F => q.1.1)
    · simpa using continuous_snd
  have hf : Continuous (Function.uncurry fun (p : F × F) (y : F) => φ ![p.1, y] * (ψ (-(y * p.2)) : ℂ)) := by
    refine (hφc.comp hrow).mul ?_
    exact continuous_subtype_val.comp (hψ.comp (continuous_snd.mul (continuous_snd.comp continuous_fst)).neg)
  have := continuous_parametric_integral_of_continuous (μ := selfDualMeasure ψ) hf (isCompact_valBall (K := F) M)
  convert this using 2 with p
  rw [pf, setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro y hy
  have : φ ![p.1, y] = 0 := by
    by_contra h
    exact hy (by simpa using (hM _ h).2)
  simp [this]

theorem exists_box_pf {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {φ : (Fin 2 → F) → ℂ} (hφ : SB φ) :
    ∃ (M : ℤ) (C : ℝ), (∀ u t, ‖pf ψ φ u t‖ ≤ C) ∧ ∀ u t, pf ψ φ u t ≠ 0 → u ∈ valBall F M ∧ t ∈ valBall F M := by
  obtain ⟨N, hN⟩ := exists_inv_sb hφ
  obtain ⟨M₁, hM₁⟩ := exists_supp_sb hφ
  obtain ⟨M₂, hM₂⟩ := partial_fourier_eventually_zero hψ1 hN
  set M := min M₁ M₂
  have hsup : ∀ u t, pf ψ φ u t ≠ 0 → u ∈ valBall F M ∧ t ∈ valBall F M := by
    intro u t h
    refine ⟨valBall_antitone (min_le_left _ _) ?_, valBall_antitone (min_le_right _ _) ?_⟩
    · by_contra hu
      exact h (pf_eq_zero_of_u hM₁ hu t)
    · by_contra ht
      exact h (hM₂ u t ht)
  have hcs : HasCompactSupport fun p : F × F => pf ψ φ p.1 p.2 := by
    refine HasCompactSupport.intro ((isCompact_valBall (K := F) M).prod (isCompact_valBall (K := F) M)) ?_
    intro p hp
    by_contra h
    exact hp ⟨(hsup _ _ h).1, (hsup _ _ h).2⟩
  obtain ⟨C, hC⟩ := (continuous_pf hψ hφ).bounded_above_of_compact_support hcs
  exact ⟨M, C, fun u t => hC (u, t), hsup⟩

theorem ind_ball_mem (n : ℤ) : (valBall F n : Set F).indicator (fun _ => (1 : ℂ)) ∈ schwartzBruhat F := by
  refine ⟨isLocallyConstant_of_add_valBall (N := n) fun x h hh => ?_, ?_⟩
  · have hiff : x + h ∈ valBall F n ↔ x ∈ valBall F n :=
      ⟨fun h' => by simpa using sub_mem h' hh, fun h' => add_mem h' hh⟩
    by_cases hx : x ∈ valBall F n
    · rw [Set.indicator_of_mem (show x + h ∈ (valBall F n : Set F) from hiff.mpr hx),
        Set.indicator_of_mem (show x ∈ (valBall F n : Set F) from hx)]
    · rw [Set.indicator_of_notMem (show x + h ∉ (valBall F n : Set F) from mt hiff.mp hx),
        Set.indicator_of_notMem (show x ∉ (valBall F n : Set F) from hx)]
  · exact HasCompactSupport.intro (isCompact_valBall n) fun x hx => Set.indicator_of_notMem hx _

def wt (n : ℤ) (τ : ℝ) (u : Fˣ) : ℝ := (valBall F n : Set F).indicator (fun _ => (1 : ℝ)) (u : F) * (modulus (u : F) : ℝ) ^ τ

theorem wt_nonneg (n : ℤ) (τ : ℝ) (u : Fˣ) : 0 ≤ wt n τ u := by
  unfold wt
  refine mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (Real.rpow_nonneg (NNReal.coe_nonneg _) _)

theorem integrable_wt (n : ℤ) {τ : ℝ} (hτ : 0 < τ) : Integrable (wt (F := F) n τ) (multHaar F) := by
  have h := integrable_localZeta (ind_ball_mem (F := F) n) (χ := 1) continuous_const (s := (τ : ℂ))
    (by simpa [quasiCharExponent] using hτ)
  refine h.norm.congr (Eventually.of_forall fun u => ?_)
  have hm : (0 : ℝ) ≤ (modulus (u : F) : ℝ) := NNReal.coe_nonneg _
  by_cases hu : (u : F) ∈ (valBall F n : Set F)
  · simp [wt, hu, Complex.norm_cpow_eq_rpow_re_of_nonneg hm, hτ.ne', abs_of_nonneg (Real.rpow_nonneg hm τ)]
  · simp [wt, hu]

theorem modulus_le_of_mem {M : ℤ} {x : F} (hx : x ∈ valBall F M) :
    (modulus x : ℝ) ≤ (residueCard F : ℝ) ^ (-M) := by
  have hq : (1 : ℝ) ≤ residueCard F := by exact_mod_cast one_lt_residueCard.le
  by_cases h0 : x = 0
  · subst h0
    simp only [modulus_zero, NNReal.coe_zero]
    positivity
  rw [modulus_of_ne_zero h0, NNReal.coe_zpow, NNReal.coe_natCast]
  exact zpow_le_zpow_right₀ hq (by have := (mem_valBall_iff_le_ord h0).mp hx; omega)

theorem torus_int {σ C : ℝ} (hσ : 0 < σ) (hC : 0 ≤ C) (M : ℤ) (T : Fˣ × Fˣ × Fˣ → ℂ) (hc : Continuous T)
    (hb : ∀ p, ‖T p‖ ≤ C * (modulus (p.1 : F) : ℝ) ^ σ)
    (hs : ∀ p, T p ≠ 0 → (p.2.1 : F) ∈ valBall F M ∧ (p.2.2 : F) ∈ valBall F M ∧
      ((p.1 * p.2.1⁻¹ : Fˣ) : F) ∈ valBall F M ∧ ((p.1 * p.2.2⁻¹ : Fˣ) : F) ∈ valBall F M) :
    Integrable T ((multHaar F).prod ((multHaar F).prod (multHaar F))) := by
  set B : ℝ := (residueCard F : ℝ) ^ (-M) with hB
  have hB0 : 0 ≤ B := by positivity
  have hD := ((integrable_wt (F := F) (M + M) (τ := σ / 2) (by positivity)).mul_prod
    ((integrable_wt (F := F) M (τ := σ / 4) (by positivity)).mul_prod
      (integrable_wt (F := F) M (τ := σ / 4) (by positivity)))).const_mul (C * (B ^ (σ / 4)) ^ 2)
  refine hD.mono' hc.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  obtain ⟨a, u₁, u₃⟩ := p
  by_cases h0 : T (a, u₁, u₃) = 0
  · rw [h0, norm_zero]
    have := wt_nonneg (F := F) (M + M) (σ / 2) a
    have := wt_nonneg (F := F) M (σ / 4) u₁
    have := wt_nonneg (F := F) M (σ / 4) u₃
    have : 0 ≤ B ^ (σ / 4) := Real.rpow_nonneg hB0 _
    positivity
  obtain ⟨h1, h3, ha1, ha3⟩ := hs _ h0
  simp only at h1 h3 ha1 ha3
  have haM : (a : F) ∈ valBall F (M + M) := by
    have := mul_mem_valBall ha1 h1
    simpa using this
  have hm : ∀ x : Fˣ, (0 : ℝ) ≤ (modulus (x : F) : ℝ) := fun x => NNReal.coe_nonneg _
  have hfac : ∀ u : Fˣ, ((a * u⁻¹ : Fˣ) : F) ∈ valBall F M →
      (modulus (a : F) : ℝ) ^ (σ / 4) ≤ B ^ (σ / 4) * (modulus (u : F) : ℝ) ^ (σ / 4) := by
    intro u hu
    rw [← Real.mul_rpow hB0 (hm u)]
    refine Real.rpow_le_rpow (hm a) ?_ (by positivity)
    have e : (a : F) = ((a * u⁻¹ : Fˣ) : F) * u := by simp
    rw [e, modulus_mul, NNReal.coe_mul]
    exact mul_le_mul_of_nonneg_right (modulus_le_of_mem hu) (hm u)
  have hsplit : (modulus (a : F) : ℝ) ^ σ = (modulus (a : F) : ℝ) ^ (σ / 2) * ((modulus (a : F) : ℝ) ^ (σ / 4) * (modulus (a : F) : ℝ) ^ (σ / 4)) := by
    have hpos : (0 : ℝ) < (modulus (a : F) : ℝ) := by exact_mod_cast modulus_pos a.ne_zero
    rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]
    congr 1
    ring
  have hw : ∀ (n : ℤ) (τ : ℝ) (u : Fˣ), (u : F) ∈ valBall F n → wt n τ u = (modulus (u : F) : ℝ) ^ τ := by
    intro n τ u hu
    simp [wt, show (u : F) ∈ (valBall F n : Set F) from hu]
  simp only [hw _ _ _ h1, hw _ _ _ h3, hw _ _ _ haM]
  have hp : ∀ (x : Fˣ) (τ : ℝ), 0 ≤ (modulus (x : F) : ℝ) ^ τ := fun x τ => Real.rpow_nonneg (hm x) τ
  have hBp : 0 ≤ B ^ (σ / 4) := Real.rpow_nonneg hB0 _
  calc ‖T (a, u₁, u₃)‖ ≤ C * (modulus (a : F) : ℝ) ^ σ := hb _
    _ = C * ((modulus (a : F) : ℝ) ^ (σ / 2) * ((modulus (a : F) : ℝ) ^ (σ / 4) * (modulus (a : F) : ℝ) ^ (σ / 4))) := by rw [hsplit]
    _ ≤ C * ((modulus (a : F) : ℝ) ^ (σ / 2) * ((B ^ (σ / 4) * (modulus (u₁ : F) : ℝ) ^ (σ / 4)) * (B ^ (σ / 4) * (modulus (u₃ : F) : ℝ) ^ (σ / 4)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (hp _ _)) hC
        exact mul_le_mul (hfac _ ha1) (hfac _ ha3) (hp _ _) (mul_nonneg hBp (hp _ _))
    _ = _ := by ring

def Jf (ψ : AddChar F Circle) (ν c : Fˣ →* ℂˣ) (s : ℂ) (φ₁ φ₃ : (Fin 2 → F) → ℂ) (t₁ t₃ : F) : ℂ :=
  ∫ p : F × F, φ₁ ![t₁, p.1] * conj (φ₃ ![t₃, p.2]) * Kr ν c s ![t₁, p.1] ![0, 1] ![t₃, p.2]
    ∂((selfDualMeasure ψ).prod (selfDualMeasure ψ))

theorem integrable_G (h4 : A4) {ψ : AddChar F Circle} (hψ : IsStd ψ) {ν c : Fˣ →* ℂˣ} (hν : IsUnit1 ν) (hc : IsUnit1 c)
    {s : ℂ} (hs : Strip s) {φ₁ φ₃ : (Fin 2 → F) → ℂ} (hφ₁ : SB φ₁) (hφ₃ : SB φ₃) :
    Integrable (fun p : (Fin 2 → F) × (Fin 2 → F) => φ₁ p.1 * conj (φ₃ p.2) * Kr ν c s p.1 ![0, 1] p.2)
      ((m2 ψ).prod (m2 ψ)) := by
  obtain ⟨-, hi⟩ := h4 F ψ hψ ν c hν hc s hs
  have hK : IsCompact (tsupport φ₁ ∪ tsupport φ₃) := hφ₁.2.isCompact.union hφ₃.2.isCompact
  set K := tsupport φ₁ ∪ tsupport φ₃ with hKdef
  have hKK := hi K hK
  have c₁ : Continuous φ₁ := hφ₁.1.continuous
  have c₃ : Continuous φ₃ := hφ₃.1.continuous
  obtain ⟨A₁, hA₁⟩ := c₁.bounded_above_of_compact_support hφ₁.2
  obtain ⟨A₃, hA₃⟩ := c₃.bounded_above_of_compact_support hφ₃.2
  have hcont : Continuous fun p : (Fin 2 → F) × (Fin 2 → F) => φ₁ p.1 * conj (φ₃ p.2) :=
    (c₁.comp continuous_fst).mul (Complex.continuous_conj.comp (c₃.comp continuous_snd))
  have hon : IntegrableOn (fun p : (Fin 2 → F) × (Fin 2 → F) => φ₁ p.1 * conj (φ₃ p.2) * Kr ν c s p.1 ![0, 1] p.2)
      (K ×ˢ K) ((m2 ψ).prod (m2 ψ)) := by
    refine Integrable.bdd_mul (c := A₁ * A₃) hKK hcont.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul (hA₁ _) (hA₃ _) (norm_nonneg _) ((norm_nonneg _).trans (hA₁ p.1))
  refine hon.integrable_of_forall_notMem_eq_zero fun p hp => ?_
  by_cases h1 : p.1 ∈ K
  · have h3 : p.2 ∉ K := fun h3 => hp ⟨h1, h3⟩
    have : φ₃ p.2 = 0 := image_eq_zero_of_notMem_tsupport fun h => h3 (Or.inr h)
    simp [this]
  · have : φ₁ p.1 = 0 := image_eq_zero_of_notMem_tsupport fun h => h1 (Or.inl h)
    simp [this]

def Rr : F × F × F × F ≃ᵐ (Fin 2 → F) × (Fin 2 → F) :=
  ((MeasurableEquiv.refl F).prodCongr MeasurableEquiv.prodAssoc.symm).trans
    (((MeasurableEquiv.refl F).prodCongr ((MeasurableEquiv.prodComm).prodCongr (MeasurableEquiv.refl F))).trans
      (((MeasurableEquiv.refl F).prodCongr MeasurableEquiv.prodAssoc).trans
        (MeasurableEquiv.prodAssoc.symm.trans
          ((MeasurableEquiv.finTwoArrow (α := F)).symm.prodCongr (MeasurableEquiv.finTwoArrow (α := F)).symm))))

theorem mp_Rr (ψ : AddChar F Circle) : MeasurePreserving (Rr (F := F))
    ((selfDualMeasure ψ).prod ((selfDualMeasure ψ).prod ((selfDualMeasure ψ).prod (selfDualMeasure ψ))))
    ((m2 ψ).prod (m2 ψ)) := by
  set d := selfDualMeasure ψ
  have hid : MeasurePreserving (MeasurableEquiv.refl F) d d := MeasurePreserving.id d
  have h1 := hid.prod ((measurePreserving_prodAssoc d d d).symm MeasurableEquiv.prodAssoc)
  have h2 := hid.prod ((Measure.measurePreserving_swap (μ := d) (ν := d)).prod hid)
  have h3 := hid.prod (measurePreserving_prodAssoc d d d)
  have h4 := (measurePreserving_prodAssoc d d (d.prod d)).symm MeasurableEquiv.prodAssoc
  have hE : MeasurePreserving (MeasurableEquiv.finTwoArrow (α := F)).symm (d.prod d) (m2 ψ) :=
    (measurePreserving_finTwoArrow d).symm _
  have h5 := hE.prod hE
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

theorem fub (h4 : A4) {ψ : AddChar F Circle} (hψ : IsStd ψ) {ν c : Fˣ →* ℂˣ} (hν : IsUnit1 ν) (hc : IsUnit1 c)
    {s : ℂ} (hs : Strip s) {φ₁ φ₃ : (Fin 2 → F) → ℂ} (hφ₁ : SB φ₁) (hφ₃ : SB φ₃) :
    ∫ t₁, ∫ t₃, Jf ψ ν c s φ₁ φ₃ t₁ t₃ ∂selfDualMeasure ψ ∂selfDualMeasure ψ =
      ∫ p : (Fin 2 → F) × (Fin 2 → F), φ₁ p.1 * conj (φ₃ p.2) * Kr ν c s p.1 ![0, 1] p.2 ∂((m2 ψ).prod (m2 ψ)) := by
  have hG := integrable_G h4 hψ hν hc hs hφ₁ hφ₃
  set G : (Fin 2 → F) × (Fin 2 → F) → ℂ := fun p => φ₁ p.1 * conj (φ₃ p.2) * Kr ν c s p.1 ![0, 1] p.2 with hGdef
  have hR := mp_Rr (F := F) ψ
  rw [← hR.integral_comp' G]
  have hH : Integrable (fun x => G (Rr x)) _ := (hR.integrable_comp_emb Rr.measurableEmbedding).2 hG
  rw [integral_prod _ hH]
  refine integral_congr_ae ?_
  filter_upwards [hH.prod_right_ae] with t₁ ht₁
  rw [integral_prod _ ht₁]
  rfl

theorem sec_mem {φ : (Fin 2 → F) → ℂ} (hφ : SB φ) (u : F) : (fun y => φ ![u, y]) ∈ schwartzBruhat F := by
  have hcont : Continuous fun y : F => (![u, y] : Fin 2 → F) := by
    refine continuous_pi fun i => ?_
    fin_cases i
    · simpa using continuous_const
    · simpa using continuous_id'
  have hemb : IsClosedEmbedding fun y : F => (![u, y] : Fin 2 → F) :=
    Function.LeftInverse.isClosedEmbedding (f := fun r : Fin 2 → F => r 1) (fun y => by simp)
      (continuous_apply 1) hcont
  exact ⟨hφ.1.comp_continuous hcont, hφ.2.comp_isClosedEmbedding hemb⟩

theorem sec_conj_mem {φ : (Fin 2 → F) → ℂ} (hφ : SB φ) (u : F) :
    (fun y => conj (φ ![u, y])) ∈ schwartzBruhat F := by
  obtain ⟨h1, h2⟩ := sec_mem hφ u
  exact ⟨h1.comp _, h2.comp_left (map_zero _)⟩

theorem mp_mul (a b : Fˣ) (w : ℂ) : mp (a * b) w = mp a w * mp b w := by
  simpa [mp, GodementSectionLocal.modPow] using GodementSectionLocal.modPow_mul (a : F) (b : F) w

theorem mp_add (a : Fˣ) (v w : ℂ) : mp a (v + w) = mp a v * mp a w := by
  simpa [mp, GodementSectionLocal.modPow] using GodementSectionLocal.modPow_add a.ne_zero v w

theorem mp_zero (a : Fˣ) : mp a 0 = 1 := by simp [mp]

theorem chF_unit (c : Fˣ →* ℂˣ) (w : ℂ) (a : Fˣ) : chF c w (a : F) = ((c a : ℂˣ) : ℂ) * mp a w := by
  simp [chF, a.ne_zero]

theorem chF_mul (c : Fˣ →* ℂˣ) (w : ℂ) (x : F) (d : Fˣ) :
    chF c w (x * d) = chF c w x * ((c d : ℂˣ) : ℂ) * mp d w := by
  by_cases hx : x = 0
  · simp [chF, hx]
  have e : Units.mk0 (x * d) (mul_ne_zero hx d.ne_zero) = Units.mk0 x hx * d := by
    ext
    simp
  simp only [chF, dif_neg hx, dif_neg (mul_ne_zero hx d.ne_zero), e, map_mul, Units.val_mul, mp_mul]
  ring

theorem kr_pt (ν c : Fˣ →* ℂˣ) (hν : IsUnit1 ν) (s : ℂ) (u₁ u₃ : Fˣ) (y₁ y₃ : F) :
    ((ν u₁ : ℂˣ) : ℂ) * conj ((ν u₃ : ℂˣ) : ℂ) * chF c⁻¹ (-s) (y₃ * ((u₃⁻¹ : Fˣ) : F) - y₁ * ((u₁⁻¹ : Fˣ) : F)) =
      Kr ν c s ![(u₁ : F), y₁] ![0, 1] ![(u₃ : F), y₃] * mp u₁ 1 * mp u₃ 1 := by
  have hd1 : dt ![(u₁ : F), y₁] ![0, 1] = u₁ := by simp [dt]
  have hd3 : dt ![(u₃ : F), y₃] ![0, 1] = u₃ := by simp [dt]
  have hd : dt ![(u₁ : F), y₁] ![(u₃ : F), y₃] =
      (y₃ * ((u₃⁻¹ : Fˣ) : F) - y₁ * ((u₁⁻¹ : Fˣ) : F)) * ((u₁ * u₃ : Fˣ) : F) := by
    simp only [dt, Units.val_mul, Units.val_inv_eq_inv_val]
    simp
    field_simp
  have hconj : conj ((ν u₃ : ℂˣ) : ℂ) = (((ν u₃)⁻¹ : ℂˣ) : ℂ) := by
    have h1 := hν.2 u₃
    rw [Units.val_inv_eq_inv_val, Complex.inv_def, Complex.normSq_eq_norm_sq, h1]
    simp
  rw [Kr, hd1, hd3, hd, chF_mul, chF_unit, chF_unit, hconj]
  set X := chF c⁻¹ (-s) (y₃ * ((u₃⁻¹ : Fˣ) : F) - y₁ * ((u₁⁻¹ : Fˣ) : F))
  have e1 : mp u₁ (s - 1) * mp u₁ (-s) * mp u₁ 1 = 1 := by
    rw [← mp_add, ← mp_add]
    have : s - 1 + -s + 1 = 0 := by ring
    rw [this, mp_zero]
  have e3 : mp u₃ (s - 1) * mp u₃ (-s) * mp u₃ 1 = 1 := by
    rw [← mp_add, ← mp_add]
    have : s - 1 + -s + 1 = 0 := by ring
    rw [this, mp_zero]
  have ec1 : ((c u₁ : ℂˣ) : ℂ) * (((c u₁)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ec3 : ((c u₃ : ℂˣ) : ℂ) * (((c u₃)⁻¹ : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul, mp_mul, mul_inv]
  have hall : (((c u₁ : ℂˣ) : ℂ) * (((c u₁)⁻¹ : ℂˣ) : ℂ)) * (((c u₃ : ℂˣ) : ℂ) * (((c u₃)⁻¹ : ℂˣ) : ℂ)) *
      ((mp u₁ (s - 1) * mp u₁ (-s) * mp u₁ 1) * (mp u₃ (s - 1) * mp u₃ (-s) * mp u₃ 1)) = 1 := by
    rw [ec1, ec3, e1, e3]
    norm_num
  linear_combination (-(((ν u₁ : ℂˣ) : ℂ) * (((ν u₃)⁻¹ : ℂˣ) : ℂ) * X)) * hall

theorem conj_pf (ψ : AddChar F Circle) (φ : (Fin 2 → F) → ℂ) (u t : F) :
    conj (pf ψ φ u t) = ∫ y, conj (φ ![u, y]) * (ψ (y * t) : ℂ) ∂selfDualMeasure ψ := by
  rw [pf, ← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [map_mul]
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj, Complex.conj_conj]

theorem conj_mp (a : Fˣ) (w : ℝ) : conj (mp a (w : ℂ)) = mp a (w : ℂ) := by
  have hm : (0 : ℝ) ≤ (modulus (a : F) : ℝ) := NNReal.coe_nonneg _
  rw [mp, ← Complex.ofReal_cpow hm, Complex.conj_ofReal]

theorem continuous_mp (s : ℂ) : Continuous fun a : Fˣ => mp a s := by
  refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
    (continuous_modulus.comp Units.continuous_val))).cpow continuous_const fun u => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (by exact_mod_cast modulus_pos u.ne_zero)

theorem norm_mp (a : Fˣ) (s : ℂ) : ‖mp a s‖ = (modulus (a : F) : ℝ) ^ s.re := by
  exact Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast modulus_pos a.ne_zero) s

def Tt (ψ : AddChar F Circle) (ν c : Fˣ →* ℂˣ) (s : ℂ) (φ₁ φ₃ : (Fin 2 → F) → ℂ) (p : Fˣ × Fˣ × Fˣ) : ℂ :=
  ((c p.1 : ℂˣ) : ℂ) * mp p.1 s * ((((ν p.2.1 : ℂˣ) : ℂ) * pf ψ φ₁ p.2.1 ((p.1 * p.2.1⁻¹ : Fˣ) : F)) *
    conj (((ν p.2.2 : ℂˣ) : ℂ) * pf ψ φ₃ p.2.2 ((p.1 * p.2.2⁻¹ : Fˣ) : F)))

theorem integrable_Tt {ψ : AddChar F Circle} (hψ : IsStd ψ) {ν c : Fˣ →* ℂˣ} (hν : IsUnit1 ν) (hc : IsUnit1 c)
    {s : ℂ} (hs : Strip s) {φ₁ φ₃ : (Fin 2 → F) → ℂ} (hφ₁ : SB φ₁) (hφ₃ : SB φ₃) :
    Integrable (Tt ψ ν c s φ₁ φ₃) ((multHaar F).prod ((multHaar F).prod (multHaar F))) := by
  obtain ⟨M₁, C₁, hb₁, hs₁⟩ := exists_box_pf hψ.1 hψ.2.1 hφ₁
  obtain ⟨M₃, C₃, hb₃, hs₃⟩ := exists_box_pf hψ.1 hψ.2.1 hφ₃
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (hb₁ 0 0)
  have hC₃ : 0 ≤ C₃ := (norm_nonneg _).trans (hb₃ 0 0)
  have hcν : Continuous fun u : Fˣ => ((ν u : ℂˣ) : ℂ) := Units.continuous_val.comp hν.1
  have hcc : Continuous fun u : Fˣ => ((c u : ℂˣ) : ℂ) := Units.continuous_val.comp hc.1
  have hpf : ∀ {φ : (Fin 2 → F) → ℂ}, SB φ → ∀ {f g : Fˣ × Fˣ × Fˣ → Fˣ}, Continuous f → Continuous g →
      Continuous fun p => pf ψ φ (f p : F) ((g p : Fˣ) : F) := fun hφ _ _ hf hg =>
    (continuous_pf hψ.1 hφ).comp ((Units.continuous_val.comp hf).prodMk (Units.continuous_val.comp hg))
  refine torus_int (σ := s.re) (C := C₁ * C₃) hs.1 (mul_nonneg hC₁ hC₃) (min M₁ M₃) _ ?_ ?_ ?_
  · unfold Tt
    refine ((hcc.comp continuous_fst).mul ((continuous_mp s).comp continuous_fst)).mul (Continuous.mul ?_ ?_)
    · exact (hcν.comp (continuous_fst.comp continuous_snd)).mul
        (hpf hφ₁ (continuous_fst.comp continuous_snd) (continuous_fst.mul (continuous_fst.comp continuous_snd).inv))
    · refine Complex.continuous_conj.comp ?_
      exact (hcν.comp (continuous_snd.comp continuous_snd)).mul
        (hpf hφ₃ (continuous_snd.comp continuous_snd) (continuous_fst.mul (continuous_snd.comp continuous_snd).inv))
  · intro p
    simp only [Tt, norm_mul, RCLike.norm_conj, hν.2, hc.2, one_mul, norm_mp]
    have := mul_le_mul (hb₁ (p.2.1 : F) ((p.1 * p.2.1⁻¹ : Fˣ) : F)) (hb₃ (p.2.2 : F) ((p.1 * p.2.2⁻¹ : Fˣ) : F)) (norm_nonneg _) hC₁
    have h0 : (0 : ℝ) ≤ (modulus (p.1 : F) : ℝ) ^ s.re := Real.rpow_nonneg (NNReal.coe_nonneg _) _
    nlinarith
  · intro p hp
    have h1 : pf ψ φ₁ p.2.1 ((p.1 * p.2.1⁻¹ : Fˣ) : F) ≠ 0 := by
      intro h
      apply hp
      simp only [Tt, h, mul_zero, zero_mul]
    have h3 : pf ψ φ₃ p.2.2 ((p.1 * p.2.2⁻¹ : Fˣ) : F) ≠ 0 := by
      intro h
      apply hp
      simp only [Tt, h, mul_zero, zero_mul, map_zero]
    exact ⟨valBall_antitone (min_le_left _ _) (hs₁ _ _ h1).1, valBall_antitone (min_le_right _ _) (hs₃ _ _ h3).1,
      valBall_antitone (min_le_left _ _) (hs₁ _ _ h1).2, valBall_antitone (min_le_right _ _) (hs₃ _ _ h3).2⟩

theorem key {ψ : AddChar F Circle} (hψ : IsStd ψ) {C₀ : ℂ}
    (h1 : ∀ G : F → ℂ, ∫ a : Fˣ, G a * mp a 1 ∂multHaar F = C₀ * ∫ t, G t ∂selfDualMeasure ψ)
    (h2 : ∀ f₁ ∈ schwartzBruhat F, ∀ f₃ ∈ schwartzBruhat F, ∀ (u₁ u₃ : Fˣ) (c : Fˣ →* ℂˣ), IsUnit1 c → ∀ s, Strip s →
      ∫ a : Fˣ, (∫ y, f₁ y * (ψ (-(y * a * (u₁⁻¹ : Fˣ))) : ℂ) ∂selfDualMeasure ψ) *
          (∫ y, f₃ y * (ψ (y * a * (u₃⁻¹ : Fˣ)) : ℂ) ∂selfDualMeasure ψ) * ((c a : ℂˣ) : ℂ) * mp a s ∂multHaar F =
        C₀ * gam ψ c⁻¹ (1 - s) * ∫ p : F × F, f₁ p.1 * f₃ p.2 * chF c⁻¹ (-s) (p.2 * (u₃⁻¹ : Fˣ) - p.1 * (u₁⁻¹ : Fˣ))
          ∂((selfDualMeasure ψ).prod (selfDualMeasure ψ)))
    (h4 : A4) {μ₁ μ₂ c : Fˣ →* ℂˣ} (hμ₁ : IsUnit1 μ₁) (hμ₂ : IsUnit1 μ₂) (hc : IsUnit1 c)
    {φ₁ φ₃ : (Fin 2 → F) → ℂ} (hφ₁ : SB φ₁) (hφ₃ : SB φ₃) {s : ℂ} (hs : Strip s) :
    Av (W2 ψ μ₁ μ₂ φ₁) (W2 ψ μ₁ μ₂ φ₃) c s 1 = C₀ ^ 3 * gam ψ c⁻¹ (1 - s) *
      ∫ p : (Fin 2 → F) × (Fin 2 → F), φ₁ p.1 * conj (φ₃ p.2) * Kr (μ₂ * μ₁⁻¹) c s p.1 ![0, 1] p.2 ∂((m2 ψ).prod (m2 ψ)) := by
  set ν := μ₂ * μ₁⁻¹ with hνd
  have hν : IsUnit1 ν := by
    refine ⟨hμ₂.1.mul hμ₁.1.inv, fun x => ?_⟩
    simp [hνd, hμ₁.2, hμ₂.2]
  have hW : ∀ (φ : (Fin 2 → F) → ℂ) (a : Fˣ), W2 ψ μ₁ μ₂ φ (dg2 a 1) = ((μ₁ a : ℂˣ) : ℂ) * mp a (1 / 2) *
      ∫ u : Fˣ, ((ν u : ℂˣ) : ℂ) * pf ψ φ u ((a * u⁻¹ : Fˣ) : F) ∂multHaar F := by
    intro φ a
    rw [whittaker_torus_integral_formula]
    congr 2
    funext u
    rw [hνd, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_comm (μ₂ u)]
  have hA : ∀ a : Fˣ, W2 ψ μ₁ μ₂ φ₁ (dg2 a 1 * 1) * conj (W2 ψ μ₁ μ₂ φ₃ (dg2 a 1 * 1)) * ((c a : ℂˣ) : ℂ) * mp a (s - 1) =
      ∫ q : Fˣ × Fˣ, Tt ψ ν c s φ₁ φ₃ (a, q) ∂((multHaar F).prod (multHaar F)) := by
    intro a
    rw [mul_one, hW, hW]
    simp only [Tt]
    rw [integral_const_mul,
      integral_prod_mul (fun u : Fˣ => ((ν u : ℂˣ) : ℂ) * pf ψ φ₁ u ((a * u⁻¹ : Fˣ) : F))
        (fun u : Fˣ => conj (((ν u : ℂˣ) : ℂ) * pf ψ φ₃ u ((a * u⁻¹ : Fˣ) : F))), integral_conj]
    set I₁ := ∫ u : Fˣ, ((ν u : ℂˣ) : ℂ) * pf ψ φ₁ u ((a * u⁻¹ : Fˣ) : F) ∂multHaar F
    set I₃ := ∫ u : Fˣ, ((ν u : ℂˣ) : ℂ) * pf ψ φ₃ u ((a * u⁻¹ : Fˣ) : F) ∂multHaar F
    have e1 : ((μ₁ a : ℂˣ) : ℂ) * conj ((μ₁ a : ℂˣ) : ℂ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hμ₁.2]
      simp
    have e2 : mp a (1 / 2) * mp a (1 / 2) * mp a (s - 1) = mp a s := by
      rw [← mp_add, ← mp_add]
      congr 1
      ring
    have e3 : conj (mp a (1 / 2)) = mp a (1 / 2) := by
      simpa using conj_mp a (1 / 2)
    simp only [map_mul, e3]
    linear_combination (I₁ * conj I₃ * ((c a : ℂˣ) : ℂ) * (mp a (1 / 2) * mp a (1 / 2) * mp a (s - 1))) * e1 +
      (I₁ * conj I₃ * ((c a : ℂˣ) : ℂ)) * e2
  have hT := integrable_Tt hψ hν hc hs hφ₁ hφ₃
  have hC : ∀ u₁ u₃ : Fˣ, ∫ a : Fˣ, Tt ψ ν c s φ₁ φ₃ (a, u₁, u₃) ∂multHaar F =
      (C₀ * gam ψ c⁻¹ (1 - s)) * (Jf ψ ν c s φ₁ φ₃ u₁ u₃ * mp u₁ 1 * mp u₃ 1) := by
    intro u₁ u₃
    have hh := h2 _ (sec_mem hφ₁ u₁) _ (sec_conj_mem hφ₃ u₃) u₁ u₃ c hc s hs
    have e : ∀ a : Fˣ, Tt ψ ν c s φ₁ φ₃ (a, u₁, u₃) = (((ν u₁ : ℂˣ) : ℂ) * conj ((ν u₃ : ℂˣ) : ℂ)) *
        ((∫ y, φ₁ ![(u₁ : F), y] * (ψ (-(y * a * (u₁⁻¹ : Fˣ))) : ℂ) ∂selfDualMeasure ψ) *
          (∫ y, conj (φ₃ ![(u₃ : F), y]) * (ψ (y * a * (u₃⁻¹ : Fˣ)) : ℂ) ∂selfDualMeasure ψ) * ((c a : ℂˣ) : ℂ) * mp a s) := by
      intro a
      simp only [Tt, map_mul, conj_pf]
      simp only [pf, Units.val_mul, mul_assoc]
      ring
    simp_rw [e]
    rw [integral_const_mul, hh, Jf]
    have hk : (((ν u₁ : ℂˣ) : ℂ) * conj ((ν u₃ : ℂˣ) : ℂ)) * (∫ p : F × F, φ₁ ![(u₁ : F), p.1] * conj (φ₃ ![(u₃ : F), p.2]) *
          chF c⁻¹ (-s) (p.2 * ((u₃⁻¹ : Fˣ) : F) - p.1 * ((u₁⁻¹ : Fˣ) : F)) ∂((selfDualMeasure ψ).prod (selfDualMeasure ψ))) =
        (∫ p : F × F, φ₁ ![(u₁ : F), p.1] * conj (φ₃ ![(u₃ : F), p.2]) * Kr ν c s ![(u₁ : F), p.1] ![0, 1] ![(u₃ : F), p.2]
          ∂((selfDualMeasure ψ).prod (selfDualMeasure ψ))) * mp u₁ 1 * mp u₃ 1 := by
      rw [← integral_const_mul, ← integral_mul_const, ← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      have := kr_pt ν c hν s u₁ u₃ p.1 p.2
      simp only
      linear_combination (φ₁ ![(u₁ : F), p.1] * conj (φ₃ ![(u₃ : F), p.2])) * this
    linear_combination (C₀ * gam ψ c⁻¹ (1 - s)) * hk
  have hL : ∫ q : Fˣ × Fˣ, ∫ a : Fˣ, Tt ψ ν c s φ₁ φ₃ (a, q) ∂multHaar F ∂((multHaar F).prod (multHaar F)) =
      C₀ ^ 3 * gam ψ c⁻¹ (1 - s) * ∫ t₁, ∫ t₃, Jf ψ ν c s φ₁ φ₃ t₁ t₃ ∂selfDualMeasure ψ ∂selfDualMeasure ψ := by
    rw [integral_prod _ hT.integral_prod_right]
    simp only [hC]
    have e : ∀ u₁ : Fˣ, ∫ u₃ : Fˣ, (C₀ * gam ψ c⁻¹ (1 - s)) * (Jf ψ ν c s φ₁ φ₃ u₁ u₃ * mp u₁ 1 * mp u₃ 1) ∂multHaar F =
        ((C₀ * gam ψ c⁻¹ (1 - s)) * C₀) * ((∫ t₃, Jf ψ ν c s φ₁ φ₃ u₁ t₃ ∂selfDualMeasure ψ) * mp u₁ 1) := by
      intro u₁
      have := h1 (Jf ψ ν c s φ₁ φ₃ u₁)
      calc _ = ((C₀ * gam ψ c⁻¹ (1 - s)) * mp u₁ 1) * ∫ u₃ : Fˣ, Jf ψ ν c s φ₁ φ₃ u₁ u₃ * mp u₃ 1 ∂multHaar F := by
            rw [← integral_const_mul]
            refine integral_congr_ae (Eventually.of_forall fun u₃ => ?_)
            simp only
            ring
        _ = _ := by rw [this]; ring
    simp only [e]
    rw [integral_const_mul, h1 fun t₁ => ∫ t₃, Jf ψ ν c s φ₁ φ₃ t₁ t₃ ∂selfDualMeasure ψ]
    ring
  rw [← fub h4 hψ hν hc hs hφ₁ hφ₃, ← hL, ← integral_integral_swap (f := fun (a : Fˣ) (q : Fˣ × Fˣ) => Tt ψ ν c s φ₁ φ₃ (a, q)) hT]
  exact integral_congr_ae (Eventually.of_forall hA)

end GlobalTheory.CompanionTheory.RankinSelbergTorusIntegrals

theorem GlobalTheory.CompanionTheory.RankinSelbergTorusIntegrals.main : Ad3.R.A2 → Ad3.R.A4 → Ad3.R.A3 := by
  intro h2 h4 F _ _ _ _ _ _ ψ hψ
  obtain ⟨C₀, hC₀, h1, h2'⟩ := h2 F ψ hψ
  exact ⟨C₀ ^ 3, pow_ne_zero _ hC₀, fun μ₁ μ₂ c hμ₁ hμ₂ hc φ₁ φ₃ hφ₁ hφ₃ s hs =>
    GlobalTheory.CompanionTheory.RankinSelbergTorusIntegrals.key hψ h1 h2' h4 hμ₁ hμ₂ hc hφ₁ hφ₃ hs⟩
