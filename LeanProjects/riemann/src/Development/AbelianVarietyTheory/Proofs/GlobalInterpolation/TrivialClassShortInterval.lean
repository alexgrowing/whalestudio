import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionZeroFreeRegionStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionUniqueSimpleExceptionalZeroStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassFamilyPsiWithExceptionalZeroStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRayClassLFunctionRealZeroFarFromOneStatement
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

namespace GlobalTheory.Hk.ShortInt

lemma one_le_ell (𝓕 : LFam) (t : ℝ) : 1 ≤ 𝓕.ell t := by
  unfold LFam.ell
  have hB := 𝓕.B_ge
  have ht := abs_nonneg t
  rw [Real.le_log_iff_exp_le (by positivity)]
  have := Real.exp_one_lt_d9
  nlinarith

lemma zeros : ∃ c₀ A c : ℝ, 0 < c₀ ∧ c₀ ≤ 1 / 20 ∧ 0 < A ∧ 0 < c ∧ c ≤ 1 ∧ ∀ 𝓕 : LFam,
    ∃ Z : AddChar 𝓕.G ℂ → Finset ℝ, (∀ χ, 𝓕.ExcZ χ c₀ (Z χ)) ∧
      (∀ χ ψ β β', β ∈ Z χ → β' ∈ Z ψ → χ = ψ ∧ β = β') ∧
      ∀ χ, ∀ β ∈ Z χ, 3 / 4 ≤ β ∧ c / 𝓕.B ^ A ≤ 1 - β := by
  obtain ⟨c4, hc4, h4⟩ := GlobalTheory.T.rayClassLFunction_zero_free_region
  obtain ⟨c5, hc5, h5⟩ := GlobalTheory.T.rayClassLFunction_unique_simple_exceptional_zero
  obtain ⟨A, c9, hA, hc9, h9⟩ := GlobalTheory.T.exists_rayClassLFunction_real_zero_far_from_one
  refine ⟨min (1 / 20) (min c4 c5), A, min c9 1, by positivity, min_le_left _ _, hA, by positivity,
    min_le_right _ _, fun 𝓕 => ?_⟩
  set c₀ := min (1 / 20) (min c4 c5) with hc₀
  have h01 : c₀ ≤ 1 / 20 := min_le_left _ _
  have h04 : c₀ ≤ c4 := (min_le_right _ _).trans (min_le_left _ _)
  have h05 : c₀ ≤ c5 := (min_le_right _ _).trans (min_le_right _ _)
  have h0 : 0 < c₀ := by positivity
  have hBpos : 0 < 𝓕.B := by linarith [𝓕.B_ge]
  have key : ∀ (χ : AddChar 𝓕.G ℂ) (s : ℂ), 1 - c₀ / 𝓕.ell s.im ≤ s.re → 𝓕.F χ s = 0 →
      3 / 4 ≤ s.re ∧ χ * χ = 1 ∧ s.im = 0 := by
    intro χ s hs hF
    have hl := one_le_ell 𝓕 s.im
    have h1 : c₀ / 𝓕.ell s.im ≤ 1 / 20 := (div_le_self h0.le hl).trans h01
    have h2 : c₀ / 𝓕.ell s.im ≤ c4 / 𝓕.ell s.im := by gcongr
    have h34 : 3 / 4 ≤ s.re := by linarith
    refine ⟨h34, ?_⟩
    by_contra hne
    have := h4 𝓕 χ s h34 hF (by tauto)
    linarith
  have keyR : ∀ (χ : AddChar 𝓕.G ℂ) (β : ℝ), 1 - c₀ / 𝓕.ell 0 ≤ β → 𝓕.F χ β = 0 →
      3 / 4 ≤ β ∧ χ * χ = 1 ∧ 1 - c5 / 𝓕.ell 0 ≤ β := by
    intro χ β hβ hF
    have := key χ β (by simpa using hβ) hF
    have hl := one_le_ell 𝓕 0
    have h2 : c₀ / 𝓕.ell 0 ≤ c5 / 𝓕.ell 0 := by gcongr
    exact ⟨by simpa using this.1, this.2.1, by linarith⟩
  have uniq : ∀ (χ ψ : AddChar 𝓕.G ℂ) (β β' : ℝ), 1 - c₀ / 𝓕.ell 0 ≤ β → 𝓕.F χ β = 0 →
      1 - c₀ / 𝓕.ell 0 ≤ β' → 𝓕.F ψ β' = 0 → χ = ψ ∧ β = β' ∧ deriv (𝓕.F χ) β ≠ 0 := by
    intro χ ψ β β' h1 h2 h3 h4
    obtain ⟨a1, a2, a3⟩ := keyR χ β h1 h2
    obtain ⟨b1, b2, b3⟩ := keyR ψ β' h3 h4
    exact h5 𝓕 χ ψ β β' a2 b2 a1 b1 a3 b3 h2 h4
  have gap : ∀ (χ : AddChar 𝓕.G ℂ) (β : ℝ), 1 - c₀ / 𝓕.ell 0 ≤ β → 𝓕.F χ β = 0 →
      min c9 1 / 𝓕.B ^ A ≤ 1 - β := by
    intro χ β h1 h2
    obtain ⟨a1, a2, a3⟩ := keyR χ β h1 h2
    refine le_trans ?_ (h9 𝓕 χ β a2 a1 h2)
    gcongr
    exact min_le_left _ _
  have ex : ∀ χ : AddChar 𝓕.G ℂ, ∃ Z : Finset ℝ,
      ∀ β : ℝ, β ∈ Z ↔ (1 - c₀ / 𝓕.ell 0 ≤ β ∧ 𝓕.F χ β = 0) := by
    intro χ
    by_cases h : ∃ β : ℝ, 1 - c₀ / 𝓕.ell 0 ≤ β ∧ 𝓕.F χ β = 0
    · obtain ⟨β, h1, h2⟩ := h
      refine ⟨{β}, fun γ => ?_⟩
      rw [Finset.mem_singleton]
      constructor
      · rintro rfl; exact ⟨h1, h2⟩
      · rintro ⟨h3, h4⟩; exact (uniq χ χ γ β h3 h4 h1 h2).2.1
    · exact ⟨∅, fun γ => ⟨fun hh => by simp at hh, fun hh => absurd ⟨γ, hh⟩ h⟩⟩
  choose Z hZ using ex
  refine ⟨Z, fun χ => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [Finset.card_le_one]
    intro a ha b hb
    rw [hZ] at ha hb
    exact (uniq χ χ a b ha.1 ha.2 hb.1 hb.2).2.1
  · intro β hβ
    rw [hZ] at hβ
    have hg := gap χ β hβ.1 hβ.2
    have : 0 < min c9 1 / 𝓕.B ^ A := by positivity
    exact ⟨hβ.1, by linarith, hβ.2, (uniq χ χ β β hβ.1 hβ.2 hβ.1 hβ.2).2.2⟩
  · intro s hs hF
    obtain ⟨_, _, him⟩ := key χ s hs hF
    have hs' : s = (s.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    refine ⟨s.re, ?_, hs'⟩
    rw [hZ]
    exact ⟨by rw [him] at hs; exact hs, by rw [← hs']; exact hF⟩
  · intro χ ψ β β' h1 h2
    rw [hZ] at h1 h2
    have := uniq χ ψ β β' h1.1 h1.2 h2.1 h2.2
    exact ⟨this.1, this.2.1⟩
  · intro χ β hβ
    rw [hZ] at hβ
    exact ⟨(keyR χ β hβ.1 hβ.2).1, gap χ β hβ.1 hβ.2⟩

lemma sum_psi (𝓕 : LFam) (u : ℝ) :
    ∑ χ : AddChar 𝓕.G ℂ, 𝓕.psi χ u =
      (((Fintype.card 𝓕.G : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, 𝓕.lam 0 n : ℝ) : ℂ) := by
  unfold LFam.psi LFam.lamChi
  rw [Finset.sum_comm]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite]
  simp

lemma exc_le {X h β δ : ℝ} (hX : Real.exp 1 ≤ X) (hh : 0 ≤ h) (hβ : 3 / 4 ≤ β) (hδ : 0 < δ)
    (hδβ : δ ≤ 1 - β) : (X * (1 + h)) ^ β / β - X ^ β / β ≤ h * X * (1 - δ / 2) := by
  have hX0 : 0 < X := (Real.exp_pos 1).trans_le hX
  have hβ0 : 0 < β := by linarith
  have h1 : (1 + h) ^ β ≤ 1 + β * h := rpow_one_add_le_one_add_mul_self (by linarith) hβ0.le (by linarith)
  have hlog : 1 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hX0]; exact hX
  have h2 : X ^ β ≤ X * (1 - δ / 2) := by
    have e1 : X ^ β = X * Real.exp (-(Real.log X * (1 - β))) := by
      rw [Real.rpow_def_of_pos hX0]
      conv_rhs => rw [← Real.exp_log hX0]
      rw [Real.log_exp, ← Real.exp_add]
      congr 1; ring
    rw [e1]
    gcongr
    have e2 : Real.exp (-(Real.log X * (1 - β))) ≤ Real.exp (-δ) := by
      apply Real.exp_le_exp.2
      nlinarith
    refine e2.trans ?_
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    have := Real.add_one_le_exp δ
    have h3 : 0 ≤ 1 - δ / 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left this h3]
  rw [Real.mul_rpow hX0.le (by linarith), ← sub_div, div_le_iff₀ hβ0]
  have hp : 0 ≤ X ^ β := by positivity
  calc X ^ β * (1 + h) ^ β - X ^ β ≤ X ^ β * (1 + β * h) - X ^ β := by gcongr
    _ = X ^ β * (β * h) := by ring
    _ ≤ X * (1 - δ / 2) * (β * h) := by gcongr
    _ = _ := by ring

lemma sum_est (𝓕 : LFam) (Z : AddChar 𝓕.G ℂ → Finset ℝ) (u E : ℝ) (hu : 0 ≤ u) (hE : 0 ≤ E)
    (h : ∀ χ : AddChar 𝓕.G ℂ, ‖𝓕.psi χ u - (if χ = 1 then (u : ℂ) else 0) +
      ∑ β ∈ Z χ, (u : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ E) :
    |(Fintype.card 𝓕.G : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, 𝓕.lam 0 n - u +
      ∑ χ, ∑ β ∈ Z χ, u ^ β / β| ≤ 𝓕.B * E := by
  have e : (((Fintype.card 𝓕.G : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, 𝓕.lam 0 n - u +
      ∑ χ, ∑ β ∈ Z χ, u ^ β / β : ℝ) : ℂ) = ∑ χ : AddChar 𝓕.G ℂ, (𝓕.psi χ u -
        (if χ = 1 then (u : ℂ) else 0) + ∑ β ∈ Z χ, (u : ℂ) ^ (β : ℂ) / (β : ℂ)) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, sum_psi, ofReal_add, ofReal_sub]
    congr 1
    · simp
    · rw [ofReal_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [ofReal_sum]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [ofReal_div, ofReal_cpow hu]
  rw [← Real.norm_eq_abs, ← Complex.norm_real, e]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ E fun χ _ => h χ).trans ?_
  rw [Finset.card_univ, AddChar.card_eq, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right 𝓕.card_le hE

lemma sum_le_of_unique {ι : Type} [Fintype ι] (Z : ι → Finset ℝ) (f : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ i j β β', β ∈ Z i → β' ∈ Z j → i = j ∧ β = β') (hf : ∀ i, ∀ β ∈ Z i, f β ≤ M) :
    ∑ i, ∑ β ∈ Z i, f β ≤ M := by
  rw [Finset.sum_sigma']
  have hc : ((Finset.univ : Finset ι).sigma Z).card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨i, a⟩ ha ⟨j, b⟩ hb
    rw [Finset.mem_sigma] at ha hb
    obtain ⟨rfl, rfl⟩ := hu i j a b ha.2 hb.2
    rfl
  refine (Finset.sum_le_card_nsmul _ _ M fun x hx => hf x.1 x.2 (Finset.mem_sigma.1 hx).2).trans ?_
  rw [nsmul_eq_mul]
  have : ((((Finset.univ : Finset ι).sigma Z).card : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hc
  nlinarith

lemma err_le {B A c c₇ c₉ C L h : ℝ} (hB : 4 ≤ B) (hA : 0 < A) (hc : 0 < c) (hc₇ : 0 < c₇) (hc₉ : 0 < c₉)
    (hC : 0 < C) (h1 : (A + 2) * c ≤ c₇ / 2) (h2 : c ≤ c₇ * c₉ / (24 * C))
    (hL : Real.log B ≤ c * L) (hh : Real.exp (-c * L) ≤ h) :
    3 * B * C * Real.exp (-c₇ * L) ≤ h * (c₉ / B ^ A) / 4 := by
  have hB0 : 0 < B := by linarith
  have hlog : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hB0]; linarith [Real.exp_one_lt_d9]
  have hcL : 1 ≤ c * L := hlog.trans hL
  have hL0 : 0 < L := by
    by_contra hn
    rw [not_lt] at hn
    nlinarith
  have a1 : B ≤ Real.exp (c * L) := by
    rw [← Real.exp_log hB0]; exact Real.exp_le_exp.2 hL
  have a2 : B ^ A ≤ Real.exp (c * L * A) := by
    rw [Real.rpow_def_of_pos hB0]; apply Real.exp_le_exp.2; gcongr
  have a3 : 12 * C ≤ c₉ * Real.exp (c₇ / 2 * L) := by
    have := Real.add_one_le_exp (c₇ / 2 * L)
    rw [le_div_iff₀ (by positivity)] at h2
    have b1 : c * (24 * C) * L ≤ c₇ * c₉ * L := by gcongr
    have b2 : 24 * C * 1 ≤ 24 * C * (c * L) := by gcongr
    nlinarith
  have hBA : 0 < B ^ A := by positivity
  have a4 : Real.exp (c * L) * Real.exp (c * L * A) * Real.exp (c₇ / 2 * L) * Real.exp (-c₇ * L) ≤
      Real.exp (-c * L) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_right h1 hL0.le]
  rw [mul_div_assoc', div_div, le_div_iff₀ (by positivity)]
  calc 3 * B * C * Real.exp (-c₇ * L) * (B ^ A * 4)
      = B * B ^ A * (12 * C) * Real.exp (-c₇ * L) := by ring
    _ ≤ Real.exp (c * L) * Real.exp (c * L * A) * (c₉ * Real.exp (c₇ / 2 * L)) * Real.exp (-c₇ * L) := by
      gcongr
    _ = Real.exp (c * L) * Real.exp (c * L * A) * Real.exp (c₇ / 2 * L) * Real.exp (-c₇ * L) * c₉ := by
      ring
    _ ≤ h * c₉ := by gcongr; exact a4.trans hh

theorem trivialClass_shortInterval : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (𝓕 : LFam) (X h : ℝ), 1 ≤ X → Real.log 𝓕.B ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / 𝓕.B ^ A ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * (1 + h)⌋₊, 𝓕.lam 0 n := by
  obtain ⟨c₀, A, c₉, hc₀, hc₀', hA, hc₉, hc₉', hz⟩ := zeros
  obtain ⟨c₇, C, hc₇, hC, h7⟩ := GlobalTheory.T.rayClassFamily_psi_with_exceptional_zero c₀ hc₀ hc₀'
  refine ⟨A + 1, min 1 (min (c₇ / 2 / (A + 2)) (c₇ * c₉ / (24 * C))), c₉ / 4, by positivity,
    by positivity, by positivity, ?_⟩
  set c := min 1 (min (c₇ / 2 / (A + 2)) (c₇ * c₉ / (24 * C))) with hcdef
  have hc : 0 < c := by positivity
  have hc1 : c ≤ 1 := min_le_left _ _
  have hc2 : (A + 2) * c ≤ c₇ / 2 := by
    have : c ≤ c₇ / 2 / (A + 2) := (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hc3 : c ≤ c₇ * c₉ / (24 * C) := (min_le_right _ _).trans (min_le_right _ _)
  intro 𝓕 X h hX hL hh hh1
  obtain ⟨Z, hZ, huniq, hgap⟩ := hz 𝓕
  have hB := 𝓕.B_ge
  have hB0 : 0 < 𝓕.B := by linarith
  have hX0 : 0 < X := by linarith
  have hh0 : 0 < h := (Real.exp_pos _).trans_le hh
  have herr := err_le hB hA hc hc₇ hc₉ hC hc2 hc3 hL hh
  have hL0 := Real.sqrt_nonneg (Real.log X)
  have hL' : Real.log 𝓕.B ≤ Real.sqrt (Real.log X) := hL.trans (mul_le_of_le_one_left hL0 hc1)
  have hlogB : 1 ≤ Real.log 𝓕.B := by
    rw [Real.le_log_iff_exp_le hB0]; linarith [Real.exp_one_lt_d9]
  have hlogX : 1 ≤ Real.log X := Real.one_le_sqrt.1 (hlogB.trans hL')
  have hXe : Real.exp 1 ≤ X := (Real.le_log_iff_exp_le hX0).1 hlogX
  have hX2 : 2 ≤ X := by linarith [Real.exp_one_gt_d9]
  have hXY : X ≤ X * (1 + h) := by nlinarith
  have hY2 : X * (1 + h) ≤ 2 * X := by nlinarith
  have hLY : Real.sqrt (Real.log X) ≤ Real.sqrt (Real.log (X * (1 + h))) :=
    Real.sqrt_le_sqrt (Real.log_le_log hX0 hXY)
  set E := Real.exp (-c₇ * Real.sqrt (Real.log X)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have e1 := sum_est 𝓕 Z X (C * X * E) hX0.le (by positivity) fun χ => h7 𝓕 χ (Z χ) X (hZ χ) hX2 hL'
  have e2 := sum_est 𝓕 Z (X * (1 + h)) (C * (2 * X) * E) (by positivity) (by positivity) fun χ =>
    (h7 𝓕 χ (Z χ) (X * (1 + h)) (hZ χ) (hX2.trans hXY) (hL'.trans hLY)).trans (by
      have : Real.exp (-c₇ * Real.sqrt (Real.log (X * (1 + h)))) ≤ E :=
        Real.exp_le_exp.2 (by nlinarith)
      gcongr)
  set δ := c₉ / 𝓕.B ^ A with hδ
  have hBA : 1 ≤ 𝓕.B ^ A := Real.one_le_rpow (by linarith) hA.le
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := (div_le_self hc₉.le hBA).trans hc₉'
  have e3 := sum_le_of_unique Z (fun β => (X * (1 + h)) ^ β / β - X ^ β / β) (h * X * (1 - δ / 2))
    (by have : 0 ≤ 1 - δ / 2 := by linarith
        positivity) huniq
    fun χ β hβ => exc_le hXe hh0.le (hgap χ β hβ).1 hδ0 (hgap χ β hβ).2
  simp only [Finset.sum_sub_distrib] at e3
  have hsplit : ∑ n ∈ Finset.Icc 1 ⌊X * (1 + h)⌋₊, 𝓕.lam 0 n = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, 𝓕.lam 0 n +
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * (1 + h)⌋₊, 𝓕.lam 0 n := by
    have := Finset.sum_Ioc_consecutive (fun n => 𝓕.lam 0 n) (Nat.zero_le ⌊X⌋₊) (Nat.floor_le_floor hXY)
    exact this.symm
  set S := ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X * (1 + h)⌋₊, 𝓕.lam 0 n with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => 𝓕.lam_nonneg 0 n
  rw [hsplit] at e2
  have e1' := (abs_le.1 e1).2
  have e2' := (abs_le.1 e2).1
  have herrX := mul_le_mul_of_nonneg_left herr hX0.le
  have main : h * X * δ / 4 ≤ (Fintype.card 𝓕.G : ℝ) * S := by nlinarith
  have main2 : h * X * δ / 4 ≤ 𝓕.B * S := main.trans (mul_le_mul_of_nonneg_right 𝓕.card_le hS0)
  rw [Real.rpow_add_one hB0.ne', ← div_div, div_le_iff₀ hB0]
  calc c₉ / 4 * h * X / 𝓕.B ^ A = h * X * δ / 4 := by rw [hδ]; ring
    _ ≤ 𝓕.B * S := main2
    _ = S * 𝓕.B := mul_comm _ _

end GlobalTheory.Hk.ShortInt
