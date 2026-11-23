import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeHtE
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePlaceMinpolyCoeffLePowMaxEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NnnormMinpolyCoeffFinitePlaceLePowStatement

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal

namespace GlobalTheory.RatCount.CoefHt

theorem mult_le_two (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) : w.mult ≤ 2 := by
  unfold InfinitePlace.mult; split_ifs <;> norm_num

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in
open Classical in

theorem exists_mulHeight_coeff_minpoly_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ),
    ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a := by
  intro F E _ _ _ _ _
  refine ⟨4 ^ (Module.finrank F E * Fintype.card (InfinitePlace F)), 2 * Module.finrank F E, fun x j => ?_⟩
  set m := Module.finrank F E with hm
  set c := (minpoly F x).coeff j with hc
  let A : InfinitePlace F → ℝ := fun w =>
    ((max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) : ℝ≥0) : ℝ)
  let B0 : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => max 1 (absFin F v ((1 : v.adicCompletion F) ⊗ₜ[F] x))
  let B : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (B0 v : ℝ)
  have hA : ∀ w, 1 ≤ A w := fun w => by simp only [A]; exact_mod_cast le_max_left _ _
  have hB : ∀ v, 1 ≤ B v := fun v => by simp only [B, B0]; exact_mod_cast le_max_left _ _
  have hB0fin : Function.HasFiniteMulSupport B0 := by
    have h := eventually_absFin_le_one (E := E) F ((1 : AF F) ⊗ₜ[F] x)
    refine (Filter.eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
    have e : compFin F E v ((1 : AF F) ⊗ₜ[F] x) = (1 : v.adicCompletion F) ⊗ₜ[F] x := by
      simp [compFin, map_one]
    rw [e] at hv'
    exact max_eq_left hv'
  have hBfin : Function.HasFiniteMulSupport B := by
    refine hB0fin.subset fun v hv hv' => hv ?_
    simp only [B, hv', NNReal.coe_one]
  have hht : (htE F x : ℝ) = (∏ w, A w) * ∏ᶠ v, B v := by
    rw [htE, NNReal.coe_mul, NNReal.coe_prod]
    congr 1
    exact (MonoidHom.map_finprod NNReal.toRealHom.toMonoidHom hB0fin)
  have hB1 : ∀ v, 1 ≤ B v ^ m := fun v => one_le_pow₀ (hB v)

  have hinf : (∏ w : InfinitePlace F, max (w c) 1 ^ w.mult) ≤
      4 ^ (m * Fintype.card (InfinitePlace F)) * (∏ w, A w) ^ (2 * m) := by
    have h1 : ∀ w : InfinitePlace F, max (w c) 1 ^ w.mult ≤ 4 ^ m * A w ^ (2 * m) := fun w => by
      have hb : 1 ≤ 2 ^ m * A w ^ m := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (hA w))
      have h2 : max (w c) 1 ≤ 2 ^ m * A w ^ m := max_le (GlobalTheory.T.infinitePlace_minpoly_coeff_le_pow_max_embeddings F E x w j) hb
      calc max (w c) 1 ^ w.mult ≤ (2 ^ m * A w ^ m) ^ w.mult :=
            pow_le_pow_left₀ (le_trans zero_le_one (le_max_right _ _)) h2 _
        _ ≤ (2 ^ m * A w ^ m) ^ 2 := pow_le_pow_right₀ hb (mult_le_two F w)
        _ = 4 ^ m * A w ^ (2 * m) := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm m 2, pow_mul, mul_comm 2 m, pow_mul]; norm_num
    calc (∏ w : InfinitePlace F, max (w c) 1 ^ w.mult) ≤ ∏ w : InfinitePlace F, (4 ^ m * A w ^ (2 * m)) :=
          Finset.prod_le_prod (fun w _ => pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _) fun w _ => h1 w
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, Finset.prod_pow]

  have hfin : (∏ᶠ v : FinitePlace F, max (v c) 1) ≤ (∏ᶠ v, B v) ^ (2 * m) := by
    have e : (∏ᶠ v : FinitePlace F, max (v c) 1) =
        ∏ᶠ v : HeightOneSpectrum (𝓞 F), max (FinitePlace.mk v c) 1 := by
      rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
      rfl
    have hle : ∀ v : HeightOneSpectrum (𝓞 F), max (FinitePlace.mk v c) 1 ≤ B v ^ m := fun v => by
      refine max_le ?_ (hB1 v)
      rw [FinitePlace.mk_apply]
      have := GlobalTheory.T.nnnorm_minpoly_coeff_finitePlace_le_pow F E x v j
      simp only [B, B0]
      exact_mod_cast this
    have hBm : Function.HasFiniteMulSupport fun v => B v ^ m := by
      refine hBfin.subset fun v hv hv' => hv ?_
      simp only [hv', one_pow]
    have hf : Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => max (FinitePlace.mk v c) 1 := by
      refine hBfin.subset fun v hv hv' => hv ?_
      exact le_antisymm ((hle v).trans (by rw [hv', one_pow])) (le_max_right _ _)
    rw [e]
    calc (∏ᶠ v : HeightOneSpectrum (𝓞 F), max (FinitePlace.mk v c) 1) ≤ ∏ᶠ v, B v ^ m :=
          finprod_le_finprod hf (fun v => le_trans zero_le_one (le_max_right _ _)) hBm hle
      _ = (∏ᶠ v, B v) ^ m := (finprod_pow hBfin m).symm
      _ ≤ (∏ᶠ v, B v) ^ (2 * m) := pow_le_pow_right₀ (one_le_finprod fun v => hB v) (by omega)
  rw [NumberField.mulHeight₁_eq, hht, mul_pow, ← mul_assoc]
  exact mul_le_mul hinf hfin (finprod_nonneg fun v => le_trans zero_le_one (le_max_right _ _))
    (mul_nonneg (by positivity) (pow_nonneg (Finset.prod_nonneg fun w _ => le_trans zero_le_one (hA w)) _))

end GlobalTheory.RatCount.CoefHt
