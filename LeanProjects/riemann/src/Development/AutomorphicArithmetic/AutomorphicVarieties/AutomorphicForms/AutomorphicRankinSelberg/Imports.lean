import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open Set UpperTheory.V.Af UpperTheory.V.Sd
open scoped ComplexConjugate

theorem UpperTheory.V.Af.Rs.cmp :
    UpperTheory.V.Af.Rs.RankSum → UpperTheory.V.Af.Rs.Rankin → UpperTheory.V.Af.Rs.ArFact → UpperTheory.V.Af.Rs.ArSum → UpperTheory.V.Af.Rs.Cmp := by
  intro hRS hR hAF hAS k L _ hk χ ψ g h hap hχ s hs
  have hrec1 : Rs.Rec (fun p => χ (p : ZMod L) * (p:ℂ)^(k-1)) (coef g.f) :=
    ⟨g.one, fun p hp n hn => g.eig p hp n hn⟩
  have hrec2 : Rs.Rec (fun p => ψ (p : ZMod L) * (p:ℂ)^(k-1)) (coef h.f) :=
    ⟨h.one, fun p hp n hn => h.eig p hp n hn⟩
  have hba : ∀ p, Nat.Prime p → coef h.f p = coef g.f p := fun p hp => hap p hp
  have hz : ∀ p, Nat.Prime p → χ (p : ZMod L) * (p:ℂ)^(k-1) ≠ ψ (p : ZMod L) * (p:ℂ)^(k-1) →
      coef g.f p = 0 := by
    intro p hp hne
    apply hχ p hp
    intro heq
    apply hne
    rw [heq]
  have hbd : ∀ p, Nat.Prime p → ‖χ (p : ZMod L) * (p:ℂ)^(k-1)‖ ≤ (p:ℝ)^(k-1) ∧
      ‖ψ (p : ZMod L) * (p:ℂ)^(k-1)‖ ≤ (p:ℝ)^(k-1) := by
    intro p hp
    constructor <;>
    · rw [norm_mul, norm_pow, Complex.norm_natCast]
      exact mul_le_of_le_one_left (by positivity) (DirichletCharacter.norm_le_one _ _)
  obtain ⟨P, hPb, hP⟩ := hAF (k-1) _ _ (coef g.f) (coef h.f) hrec1 hrec2 hba hz hbd
  have hkt : ((k-1 : ℕ) : ℝ) + 1 ≤ (k:ℝ) + s - 1 := by
    rw [Nat.cast_sub hk]
    push_cast
    linarith [hs.1]
  have key := hAS (k-1) ((k:ℝ) + s - 1) (coef g.f) (coef h.f) P hkt hPb hP (hRS k L g.f s hs)
  rw [hR k L g.f g.f s hs, hR k L g.f h.f s hs, norm_mul, norm_mul]
  have hconv : (∑' n : ℕ, (starRingEnd ℂ) (coef g.f n) * coef g.f n / (((n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ))
      = ((∑' n : ℕ, ‖coef g.f n‖ ^ 2 / (n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1
    funext n
    rw [Complex.conj_mul']
    push_cast
    ring
  have hnn : 0 ≤ ∑' n : ℕ, ‖coef g.f n‖ ^ 2 / (n:ℝ) ^ ((k:ℝ) + s - 1) :=
    tsum_nonneg fun n => div_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  rw [hconv, Complex.norm_of_nonneg hnn]
  have hre := Complex.re_le_norm (∑' n : ℕ, (starRingEnd ℂ) (coef h.f n) * coef g.f n /
    (((n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ))
  have hg := norm_nonneg ((Rs.gam ((k:ℝ) + s - 1) : ℝ) : ℂ)
  calc _ ≤ ‖((Rs.gam ((k:ℝ) + s - 1) : ℝ) : ℂ)‖ * (7 * ‖∑' n : ℕ, (starRingEnd ℂ) (coef h.f n) * coef g.f n /
        (((n:ℝ) ^ ((k:ℝ) + s - 1) : ℝ) : ℂ)‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hg
    _ = _ := by ring
