import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherTail

noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.SzRules

variable {l : ℕ} [hl : Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem norm_natCast_eq (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  have h : (n : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (n : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_le_one_of_isIntegral {y : ℂ_[l]} (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral ..)

theorem mem_of_natCast_mul {n : ℕ} (hn : n ≠ 0) {x : ℂ} (h : (n : ℂ) * x ∈ algebraicClosure ℚ ℂ) :
    x ∈ algebraicClosure ℚ ℂ := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have := div_mem h (natCast_mem (algebraicClosure ℚ ℂ) n)
  rwa [mul_div_cancel_left₀ _ hn'] at this

theorem norm_natCast_mul (n : ℕ) {x : ℂ} (hx : x ∈ algebraicClosure ℚ ℂ) (h : (n : ℂ) * x ∈ algebraicClosure ℚ ℂ) :
    ‖lam ⟨(n : ℂ) * x, h⟩‖ = ‖(n : ℚ_[l])‖ * ‖lam ⟨x, hx⟩‖ := by
  have : (⟨(n : ℂ) * x, h⟩ : algebraicClosure ℚ ℂ) = (n : algebraicClosure ℚ ℂ) * ⟨x, hx⟩ := rfl
  rw [this, map_mul, map_natCast, norm_mul, norm_natCast_eq]

theorem sz_of_isIntegral (n : ℕ) (x : ℂ) (hn : ¬ l ∣ n) (h : IsIntegral ℤ ((n : ℂ) * x)) : Sz l lam 0 x := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hm : (n : ℂ) * x ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff'.2 h.tower_top
  have hx := mem_of_natCast_mul hn0 hm
  refine ⟨hx, ?_⟩
  have h1 : IsIntegral ℤ (⟨(n : ℂ) * x, hm⟩ : algebraicClosure ℚ ℂ) :=
    (isIntegral_algHom_iff (algebraicClosure ℚ ℂ).val.toRingHom.toIntAlgHom Subtype.val_injective).1 h
  have h2 : ‖lam ⟨(n : ℂ) * x, hm⟩‖ ≤ 1 :=
    norm_le_one_of_isIntegral (by convert map_isIntegral_int lam h1; exact Subsingleton.elim _ _)
  have h3 : ‖(n : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hn
  have h4 := norm_natCast_mul (lam := lam) n hx hm
  rw [h3, one_mul] at h4
  rw [Real.rpow_zero, ← h4]
  exact h2

theorem sz_add {r : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r y) : Sz l lam r (x + y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨add_mem hx hy, ?_⟩
  have : (⟨x + y, add_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [this, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' hy')

theorem sz_mul {r₁ r₂ : ℝ} {x y : ℂ} (hx : Sz l lam r₁ x) (hy : Sz l lam r₂ y) :
    Sz l lam (r₁ + r₂) (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, norm_mul, Real.rpow_add (by exact_mod_cast hl.out.pos)]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r r' : ℝ} {x : ℂ} (h : r ≤ r') (hx : Sz l lam r x) : Sz l lam r' x := by
  obtain ⟨hx, hx'⟩ := hx
  exact ⟨hx, hx'.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_lt.le) h)⟩

theorem sz_neg {r : ℝ} {x : ℂ} (hx : Sz l lam r x) : Sz l lam r (-x) := by
  obtain ⟨hx, hx'⟩ := hx
  refine ⟨neg_mem hx, ?_⟩
  have : (⟨-x, neg_mem hx⟩ : algebraicClosure ℚ ℂ) = -⟨x, hx⟩ := rfl
  rwa [this, map_neg, norm_neg]

theorem sz_prime_mul (r : ℝ) (x : ℂ) : Sz l lam r ((l : ℂ) * x) ↔ Sz l lam (r + 1) x := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  constructor
  · rintro ⟨h, h'⟩
    have hx := mem_of_natCast_mul hl.out.ne_zero h
    refine ⟨hx, ?_⟩
    rw [norm_natCast_mul l hx h, Padic.norm_p, inv_mul_le_iff₀ hl0] at h'
    rw [Real.rpow_add_one hl0.ne', mul_comm]
    exact h'
  · rintro ⟨hx, h'⟩
    have h : (l : ℂ) * x ∈ algebraicClosure ℚ ℂ := mul_mem (natCast_mem _ l) hx
    refine ⟨h, ?_⟩
    rw [norm_natCast_mul l hx h, Padic.norm_p, inv_mul_le_iff₀ hl0]
    rw [Real.rpow_add_one hl0.ne', mul_comm] at h'
    exact h'

theorem sz_of_sq {r : ℝ} {x : ℂ} (h : Sz l lam r (x ^ 2)) : Sz l lam (r / 2) x := by
  obtain ⟨h, h'⟩ := h
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hx : x ∈ algebraicClosure ℚ ℂ :=
    mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by norm_num : 0 < 2) (mem_algebraicClosure_iff.1 h))
  refine ⟨hx, ?_⟩
  have : (⟨x ^ 2, h⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ ^ 2 := rfl
  rw [this, map_pow, norm_pow] at h'
  have e : (l : ℝ) ^ r = ((l : ℝ) ^ (r / 2)) ^ 2 := by
    rw [sq, ← Real.rpow_add hl0]; congr 1; ring
  rw [e] at h'
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ (n : ℕ) (x : ℂ), ¬ l ∣ n → IsIntegral ℤ ((n : ℂ) * x) → Sz l lam 0 x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y)) ∧ (∀ (r r' : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r' y → Sz l lam (r + r') (x * y)) ∧ (∀ (r r' : ℝ) (x : ℂ), r ≤ r' → Sz l lam r x → Sz l lam r' x) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r x → Sz l lam r (-x)) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r ((l : ℂ) * x) ↔ Sz l lam (r + 1) x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r (x ^ 2) → y = x → Sz l lam (r / 2) y) :=
  fun _ _ _ => ⟨sz_of_isIntegral, fun _ _ _ => sz_add, fun _ _ _ _ => sz_mul, fun _ _ _ => sz_mono, fun _ _ => sz_neg,
    sz_prime_mul, fun _ _ _ h e => e ▸ sz_of_sq h⟩

end GlobalTheory.SzRules
