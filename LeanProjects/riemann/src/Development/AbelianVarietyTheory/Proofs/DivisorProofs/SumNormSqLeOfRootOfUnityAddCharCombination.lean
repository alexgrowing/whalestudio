import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.ParsevalRootsOfUnity

theorem isIntegral_of_pow_eq_one {R : Type} [CommRing R] (z : R) (m : ℕ) (hm : 0 < m)
    (h : z ^ m = 1) : IsIntegral ℤ z :=
  ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', by simp [h]⟩

theorem mem_Qbar_of_pow_eq_one (z : ℂ) (m : ℕ) (hm : 0 < m) (h : z ^ m = 1) : z ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact ((isIntegral_of_pow_eq_one z m hm h).tower_top (A := ℚ)).isAlgebraic

theorem norm_eq_one_of_pow_eq_one' (z : ℂ) (m : ℕ) (hm : 0 < m) (h : z ^ m = 1) : ‖z‖ = 1 :=
  (pow_eq_one_iff_of_nonneg (norm_nonneg z) hm.ne').1 (by rw [← norm_pow, h, norm_one])

theorem exists_integral_coeffs_sum_norm_sq_le_of_rootOfUnity : ∀ {ι Q : Type} [Fintype ι] [Fintype Q] [AddCommGroup Q] (N k : ℕ) (c : ι → ℂ) (χ : ι → AddChar Q ℂ), 0 < N → (∀ i, ∃ m : ℕ, 0 < m ∧ c i ^ m = 1) → Function.Injective χ → Fintype.card Q = N ^ k → Fintype.card ι ≤ N ^ k → ∃ r : Q → Qbar, (∀ q, (r q : ℂ) = ((N : ℂ) ^ k)⁻¹ * ∑ i, c i * χ i q) ∧ (∀ q, IsIntegral ℤ ((N : Qbar) ^ k * r q)) ∧ ∀ ρ : Qbar →+* ℂ, (∑ q, ‖ρ (r q)‖) ^ 2 ≤ (N : ℝ) ^ k := by
  intro ι Q _ _ _ N k c χ hN hc hχ hQ hι
  classical
  choose m hm hcm using hc
  have hQpos : 0 < Fintype.card Q := Fintype.card_pos
  have hχq : ∀ i q, χ i q ^ Fintype.card Q = 1 := fun i q => by
    rw [← AddChar.map_nsmul_eq_pow, card_nsmul_eq_zero, AddChar.map_zero_eq_one]
  let cq : ι → Qbar := fun i => ⟨c i, mem_Qbar_of_pow_eq_one _ _ (hm i) (hcm i)⟩
  let xq : ι → Q → Qbar := fun i q => ⟨χ i q, mem_Qbar_of_pow_eq_one _ _ hQpos (hχq i q)⟩
  have hNQ : (N : Qbar) ≠ 0 := by exact_mod_cast hN.ne'
  let r : Q → Qbar := fun q => ((N : Qbar) ^ k)⁻¹ * ∑ i, cq i * xq i q
  refine ⟨r, ?_, ?_, ?_⟩
  · intro q
    simp [r, cq, xq]
  · intro q
    have : (N : Qbar) ^ k * r q = ∑ i, cq i * xq i q := by
      simp only [r]
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hNQ), one_mul]
    rw [this]
    refine IsIntegral.sum _ fun i _ => IsIntegral.mul ?_ ?_
    · exact isIntegral_of_pow_eq_one _ (m i) (hm i) (Subtype.ext (by simpa [cq] using hcm i))
    · exact isIntegral_of_pow_eq_one _ _ hQpos (Subtype.ext (by simpa [xq] using hχq i q))
  · intro ρ
    let χ' : ι → AddChar Q Qbar := fun i =>
      { toFun := xq i
        map_zero_eq_one' := Subtype.ext (by simp [xq])
        map_add_eq_mul' := fun a b => Subtype.ext (by simp [xq, AddChar.map_add_eq_mul]) }
    let ψ : ι → AddChar Q ℂ := fun i => (ρ : Qbar →* ℂ).compAddChar (χ' i)
    have hψ : ∀ i q, ψ i q = ρ (xq i q) := fun i q => rfl
    let a : ι → ℂ := fun i => ρ (cq i)
    have ha : ∀ i, a i * (starRingEnd ℂ) (a i) = 1 := by
      intro i
      have h1 : a i ^ m i = 1 := by
        simp only [a]
        rw [← map_pow]
        have : cq i ^ m i = 1 := Subtype.ext (by simpa [cq] using hcm i)
        rw [this, map_one]
      rw [Complex.mul_conj', norm_eq_one_of_pow_eq_one' _ _ (hm i) h1]
      simp
    have hinj : Function.Injective ψ := by
      intro i j hij
      apply hχ
      ext q
      have h1 : ρ (xq i q) = ρ (xq j q) := by rw [← hψ, ← hψ, hij]
      have h2 := congrArg Subtype.val (ρ.injective h1)
      simpa [xq] using h2
    have horth : ∀ i j, ∑ q, ψ i q * (starRingEnd ℂ) (ψ j q) = if i = j then (Fintype.card Q : ℂ) else 0 := by
      intro i j
      have : ∀ q, ψ i q * (starRingEnd ℂ) (ψ j q) = (ψ i - ψ j) q := fun q => by
        rw [AddChar.sub_apply, AddChar.map_neg_eq_conj]
      simp_rw [this]
      rw [AddChar.sum_eq_ite]
      by_cases h : i = j
      · simp [h]
      · have : ψ i - ψ j ≠ 0 := fun h' => h (hinj (sub_eq_zero.1 h'))
        simp [h, this]
    let f : Q → ℂ := fun q => ∑ i, a i * ψ i q
    have hpars : ∑ q, ‖f q‖ ^ 2 = (Fintype.card Q : ℝ) * Fintype.card ι := by
      apply Complex.ofReal_injective
      push_cast
      simp_rw [← Complex.mul_conj']
      calc ∑ q, f q * (starRingEnd ℂ) (f q)
          = ∑ q, ∑ i, ∑ j, (a i * (starRingEnd ℂ) (a j)) * (ψ i q * (starRingEnd ℂ) (ψ j q)) := by
            refine Finset.sum_congr rfl fun q _ => ?_
            simp only [f, map_sum, map_mul, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            ring
        _ = ∑ i, ∑ j, (a i * (starRingEnd ℂ) (a j)) * ∑ q, (ψ i q * (starRingEnd ℂ) (ψ j q)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_comm]
            simp [Finset.mul_sum]
        _ = ∑ i, (Fintype.card Q : ℂ) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [horth, ha]
        _ = (Fintype.card Q : ℂ) * Fintype.card ι := by
            simp [mul_comm]
    have hCS : (∑ q, ‖f q‖) ^ 2 ≤ (Fintype.card Q : ℝ) * ∑ q, ‖f q‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Q)) (f := fun q => ‖f q‖)
      simpa using this
    have hρr : ∀ q, ‖ρ (r q)‖ = ((N : ℝ) ^ k)⁻¹ * ‖f q‖ := by
      intro q
      simp only [r, map_mul, map_inv₀, map_pow, map_natCast, map_sum, norm_mul, norm_inv,
        norm_pow, Complex.norm_natCast, f, a, hψ]
    simp_rw [hρr]
    rw [← Finset.mul_sum, mul_pow]
    have hNk : (0 : ℝ) < (N : ℝ) ^ k := by positivity
    have hQr : (Fintype.card Q : ℝ) = (N : ℝ) ^ k := by exact_mod_cast hQ
    have hιr : (Fintype.card ι : ℝ) ≤ (N : ℝ) ^ k := by exact_mod_cast hι
    calc (((N : ℝ) ^ k)⁻¹) ^ 2 * (∑ q, ‖f q‖) ^ 2
        ≤ (((N : ℝ) ^ k)⁻¹) ^ 2 * ((Fintype.card Q : ℝ) * ((Fintype.card Q : ℝ) * (Fintype.card ι : ℝ))) := by
          gcongr
          rw [← hpars]; exact hCS
      _ = (Fintype.card ι : ℝ) := by
          rw [hQr]; field_simp
      _ ≤ (N : ℝ) ^ k := hιr

end GlobalTheory.ParsevalRootsOfUnity
