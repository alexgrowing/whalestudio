import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionDiagonalActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionActionBoundedMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBoxBoundedValuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
open ValuativeRel Matrix

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.RankCoinv

theorem GlobalTheory.RankCoinv.boxFn_mem_lowRank_succ_sup_twistSpan_of_zero_row : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (i₀ : A) (r c m : ℕ) (C : Matrix A D k) (H : Matrix (Fin r) A k) (Q : Matrix D (Fin r) k), (∀ l, H l i₀ = 0) → (∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k)) → c + 1 ≤ m → (∀ l j, (H * C) l j ∈ 𝒪[k]) → (∀ j l, Q j l ∈ 𝒪[k]) → H * C * Q = 1 → (∀ j, C i₀ j = 0) → GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hν1 i₀ r c m C H Q hH0 hHv hcm hHC hQ hHCQ hC0
  set g : Matrix A D k → ℂ := boxFn ϖ C (fun _ => m) with hg
  set g' : Matrix A D k → ℂ := boxFn ϖ C (Function.update (fun _ => m) i₀ (m - 1)) with hg'
  set lam : ℂ := (((ν ϖ)⁻¹ : ℂˣ) : ℂ) * apow ϖ (-(Fintype.card D : ℂ) / 2) with hlam
  set N : ℕ := Fintype.card (Fin r → Res k 1) with hN
  let F : (Fin r → Res k 1) → Matrix A D k → ℂ := fun b => boxFn ϖ (Matrix.updateRow C i₀
    ((fun l => (ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ᵥ* (H * C))) (fun _ => m)

  have hz := GlobalTheory.T.box_function_diagonal_action k A D ϖ ν β i₀ C hC0 m (m - 1)
  have hupd : Function.update (fun _ : A => m) i₀ m = fun _ => m := Function.update_eq_self _ _
  rw [Nat.sub_add_cancel (by omega : 1 ≤ m), hupd] at hz
  have h3 : lam • g - g' ∈ twistSpan ν β := by
    rw [hlam, hg, ← hz]; exact sub_mem_twistSpan ν β _ (boxFn_mem_SB _ _ _)

  have h1 : g' - ∑ b, F b ∈ lowRank (r + 1) :=
    GlobalTheory.T.integral_box_bounded_valuation k A D ϖ hϖ i₀ r c m C H Q hH0 hHv hcm hHC hQ hHCQ hC0

  have hv1 : valuation k (ϖ : k) ≤ 1 := by rw [hϖ]; exact (uniformizer_lt_one (R := k)).le
  have h2 : ∀ b, F b - g ∈ twistSpan ν β := by
    intro b
    have ht : ∀ l, valuation k ((ϖ : k) ^ (m - 1) * ((Quotient.out (b l) : 𝒪[k]) : k)) ≤
        valuation k ((ϖ ^ c : kˣ) : k) := by
      intro l
      have hout : valuation k ((Quotient.out (b l) : 𝒪[k]) : k) ≤ 1 := (Quotient.out (b l)).2
      rw [map_mul, map_pow, Units.val_pow_eq_pow_val, map_pow]
      exact (mul_le_of_le_one_right' hout).trans (pow_le_pow_right_of_le_one' hv1 (by omega))
    have hu := GlobalTheory.T.box_function_action_bounded_matrix k A D ϖ ν β i₀ r c m C H _ hH0 hHv ht
    have hrow : C i₀ = 0 := funext hC0
    rw [hrow, zero_add] at hu
    exact hu

  have key : (lam - (N : ℂ)) • g ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    have e : (lam - (N : ℂ)) • g = (g' - ∑ b, F b) + ∑ b, (F b - g) + (lam • g - g') := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, sub_smul, Nat.cast_smul_eq_nsmul ℂ]
      abel
    rw [e]
    exact add_mem (add_mem (Submodule.mem_sup_left h1)
      (Submodule.mem_sup_right (Submodule.sum_mem _ fun b _ => h2 b))) (Submodule.mem_sup_right h3)

  have hne : lam - (N : ℂ) ≠ 0 := by
    intro h
    have hl : lam = N := sub_eq_zero.1 h
    set a : ℝ := nabs k ϖ ^ (-(Fintype.card D : ℝ) / 2) with ha_def
    have hapos : 0 < a := Real.rpow_pos_of_pos (nabs_pos ϖ) _
    have ha : apow ϖ (-(Fintype.card D : ℂ) / 2) = (a : ℂ) := by
      rw [apow, ha_def, Complex.ofReal_cpow (nabs_pos ϖ).le]
      push_cast; ring_nf
    set u : ℂ := (((ν ϖ)⁻¹ : ℂˣ) : ℂ) with hu_def
    have hua : u * a = N := by rw [← ha]; exact hl
    have hu : u = ((N / a : ℝ) : ℂ) := by
      have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hapos.ne'
      rw [Complex.ofReal_div, Complex.ofReal_natCast, ← hua, mul_div_cancel_right₀ _ ha0]
    have hnorm : ‖u‖ = 1 := by
      rw [hu_def, Units.val_inv_eq_inv_val, norm_inv, hν, inv_one]
    rw [hu, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (Nat.cast_nonneg _) hapos.le)] at hnorm
    have hu1 : u = 1 := by rw [hu, hnorm]; simp
    apply hν1
    have : (ν ϖ)⁻¹ = 1 := Units.ext (by simpa [hu_def] using hu1)
    exact inv_eq_one.1 this
  exact (Submodule.smul_mem_iff _ hne).1 key
