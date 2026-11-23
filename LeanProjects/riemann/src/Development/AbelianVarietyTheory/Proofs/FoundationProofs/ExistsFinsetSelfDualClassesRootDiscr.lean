import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FiniteClassesSelfDualOfSelfDual
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFinsetSelfDualClassesHerm

open NumberField Module Submodule
open ReciprocityTheory.ChartRestriction.G.FD (herm cc fdeg rdE)

namespace GlobalTheory

namespace RootClassCount

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isIntegral_herm_iff {n : ℕ} (x y : Fin n → E) :
    IsIntegral ℤ (herm 1 y x) ↔ IsIntegral ℤ (∑ i, IsCMField.complexConj E (x i) * y i) := by
  rw [DualFamily.herm_one_eq]
  simp only [cc, mul_comm]

theorem mul_conjTranspose_eq_one {n : ℕ} (γ : Matrix (Fin n) (Fin n) E)
    (h : ∀ x y, herm 1 (γ.mulVec x) (γ.mulVec y) = herm 1 x y) :
    γ * (γ.map (IsCMField.complexConj E)).transpose = 1 := by
  rw [mul_eq_one_comm]
  ext i j
  have := h (Pi.single j 1) (Pi.single i 1)
  rw [DualFamily.herm_one_eq, DualFamily.herm_one_eq] at this
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, cc] at this
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, mul_comm, Matrix.one_apply]
  rw [this]
  simp [Pi.single_apply, eq_comm]

omit [IsCMField E] in
theorem rdE_eq : rdE E = |(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) := rfl

omit [IsCMField E] in
theorem one_le_rootDiscr : 1 ≤ |(discr E : ℝ)| ^ ((1 : ℝ) / (finrank ℚ E : ℝ)) := by
  refine Real.one_le_rpow ?_ (by positivity)
  exact_mod_cast Int.one_le_abs (discr_ne_zero E)

theorem exists_bounded_basis {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hint : ∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ L, IsIntegral ℤ (herm 1 x y)) → x ∈ L) :
    ∃ v : Fin n → Fin n → E, (∀ i, v i ∈ L) ∧ LinearIndependent E v ∧
      ∀ (σ : E →+* ℂ) (i k : Fin n), ‖σ (herm 1 (v i) (v k))‖ ≤
        4 * (fdeg E : ℝ) ^ 3 * n ^ 4 * rdE E ^ 2 := by
  obtain ⟨v, hv, hli, -, hle⟩ := exists_short_vectors L hfg hint hdual
  obtain ⟨s, hs1, hs2, -⟩ := euclidean_basis_exists E (Fin n → E) _ v hli (by
    simp [ShortVectors.finrank_eq])
  have hsr : s.card = n := by simpa using hs1
  let e : Fin n ≃ s := (s.equivFinOfCardEq hsr).symm
  have h3 : ((fdeg E : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (fdeg E : ℝ) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_natCast]
    norm_num
  refine ⟨fun i => v (e i), fun i => hv _, hs2.comp e e.injective, fun σ i k => ?_⟩
  refine (SelfDualClasses.norm_herm_le σ _ _ _ (hle _ σ) (hle _ σ)).trans (le_of_eq ?_)
  rw [mul_pow, mul_pow, mul_pow, h3]
  ring

theorem bound_le (f n : ℕ) {r : ℝ} (hf : 0 < f) (hr : 1 ≤ r) :
    (1 + 2 * (4 * (f : ℝ) ^ 3 * n ^ 4 * r ^ 2)) ^ (2 * f * n ^ 2) *
      (n * (4 * (f : ℝ) ^ 3 * n ^ 4 * r ^ 2)) ^ (2 * f * n ^ 2) ≤
      (3 * (((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * r ^ 2)) ^ (3 * (2 * f) * n ^ 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set p : ℝ := ((2 * f : ℕ) : ℝ) ^ 2 * (n : ℝ) ^ 4 * r ^ 2 with hp
  have hp' : p = 4 * (f : ℝ) ^ 2 * (n : ℝ) ^ 4 * r ^ 2 := by rw [hp]; push_cast; ring
  have hB : 4 * (f : ℝ) ^ 3 * n ^ 4 * r ^ 2 = f * p := by rw [hp']; ring
  have h1 : (f : ℝ) ^ 2 * n ≤ p := by
    rw [hp']
    have h2 : (n : ℝ) ≤ n ^ 4 := le_self_pow₀ hn' (by norm_num)
    have h3 : 1 ≤ r ^ 2 := one_le_pow₀ hr
    calc (f : ℝ) ^ 2 * n = 1 * (f : ℝ) ^ 2 * n * 1 := by ring
      _ ≤ _ := by gcongr; norm_num
  have h4 : 1 ≤ (f : ℝ) ^ 2 * n := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hf') hn'
  have h5 : 1 ≤ p := h4.trans h1
  have h6 : 1 ≤ f * p := one_le_mul_of_one_le_of_one_le hf' h5
  rw [hB, ← mul_pow, mul_assoc 3, pow_mul _ 3]
  gcongr
  calc (1 + 2 * (f * p)) * (n * (f * p)) ≤ (3 * (f * p)) * (n * (f * p)) := by
        gcongr; linarith
    _ = 3 * ((f : ℝ) ^ 2 * n) * p ^ 2 := by ring
    _ ≤ 27 * p * p ^ 2 := by gcongr; norm_num
    _ = _ := by ring

end RootClassCount

open RootClassCount in

theorem exists_finset_selfDual_classes_rootDiscr :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    ∃ R : Finset (Submodule (𝓞 E) (Fin n → E)),
      (R.card : ℝ) ≤ (3 * ((Module.finrank ℚ E : ℝ) ^ 2 * (n : ℝ) ^ 4 *
        (|(discr E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ E : ℝ))) ^ 2)) ^
          (3 * Module.finrank ℚ E * n ^ 2) ∧
      ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ →
        (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (∑ i, IsCMField.complexConj E (x i) * y i)) →
        ∃ L₀ ∈ R, ∃ γ : Matrix (Fin n) (Fin n) E,
          γ * (γ.map (IsCMField.complexConj E)).transpose = 1 ∧
          ∀ x, x ∈ L₀ ↔ γ.mulVec x ∈ L := by
  intro E _ _ _ n
  obtain ⟨R, -, h2, h3⟩ := ClassCount.exists_finset_classes (K := E) (r := n) (G := 1)
    {L | L.FG ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (herm 1 y x)}
    (B := 4 * (fdeg E : ℝ) ^ 3 * n ^ 4 * rdE E ^ 2) (by positivity) fun L hL =>
      ⟨by simp, fun x hx => (hL.2 x).1 hx,
        exists_bounded_basis L hL.1 (fun x hx => (hL.2 x).1 hx) fun x hx => (hL.2 x).2 hx⟩
  refine ⟨R, h3.trans ?_, fun L hfg _ hsd => ?_⟩
  · have h := bound_le (fdeg E) n ClassCount.fdeg_pos (one_le_rootDiscr (E := E))
    rw [← ShortVectors.finrank_eq] at h
    rw [rdE_eq, ← ShortVectors.finrank_eq]
    exact h
  · obtain ⟨L₀, hL₀, γ, hγ, hm⟩ := h2 L ⟨hfg, fun y => by
      simp only [isIntegral_herm_iff]; exact hsd y⟩
    exact ⟨L₀, hL₀, γ, mul_conjTranspose_eq_one _ hγ, hm⟩

end GlobalTheory
