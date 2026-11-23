import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.ThmSUniform
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open DworkIntegrality (Bd bd_add bd_sub bd_neg bd_mul bd_C int_mul int_pow frob_congr PhiH PhiH_apply)

namespace CoefficientSupportCongruences

open FrobeniusSubstitution

section Supp

variable {K : Type} [Field K]

private theorem exists_pow_of_coeff_AA_ne_zero {p : ℕ} {x y : Fin 2} {n : Fin 2 →₀ ℕ}
    (h : MvPowerSeries.coeff n (AA K p x y) ≠ 0) :
    ∃ i j : ℕ, n x = (p ^ 2) ^ i ∧ n y = p * (p ^ 2) ^ j := by
  have h' : AA K p x y n ≠ 0 := h
  simp only [AA] at h'
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hi
  split_ifs at hj with hc
  · exact ⟨i, j, hc.2.1, hc.2.2⟩
  · exact absurd rfl hj

private theorem pow_sq_pow_modEq_one_sq_sub_one {p : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    (p ^ 2) ^ i ≡ 1 [MOD p ^ 2 - 1] := by
  have key : p ^ 2 ≡ 1 [MOD p ^ 2 - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ (by omega))
  simpa using key.pow i

theorem support_ok_a_zero_one {p : ℕ} (hp : 2 ≤ p) : SuppOK p (AA K p 0 1) := by
  intro n hn
  obtain ⟨i, j, hi, hj⟩ := exists_pow_of_coeff_AA_ne_zero hn
  have hp0 : 0 < p := by omega
  rw [hi, hj]
  refine ⟨pow_pos (pow_pos hp0 2) i, Nat.mul_pos hp0 (pow_pos (pow_pos hp0 2) j), ?_⟩
  have h2 : p * (p * (p ^ 2) ^ j) = (p ^ 2) ^ (j + 1) := by ring
  rw [h2]
  exact (pow_sq_pow_modEq_one_sq_sub_one hp i).trans (pow_sq_pow_modEq_one_sq_sub_one hp (j + 1)).symm

theorem support_ok_a_one_zero {p : ℕ} (hp : 2 ≤ p) : SuppOK p (AA K p 1 0) := by
  intro n hn
  obtain ⟨i, j, hi, hj⟩ := exists_pow_of_coeff_AA_ne_zero hn
  have hp0 : 0 < p := by omega
  rw [hi, hj]
  refine ⟨Nat.mul_pos hp0 (pow_pos (pow_pos hp0 2) j), pow_pos (pow_pos hp0 2) i, ?_⟩
  exact ((pow_sq_pow_modEq_one_sq_sub_one hp j).mul_left p).trans ((pow_sq_pow_modEq_one_sq_sub_one hp i).mul_left p).symm

private theorem suppOK_C_mul_sub_C_mul {p : ℕ} {G H : MvPowerSeries (Fin 2) K} (hG : SuppOK p G)
    (hH : SuppOK p H) (a b : K) :
    SuppOK p (MvPowerSeries.C a * G - MvPowerSeries.C b * H) := by
  intro n hn
  by_cases h1 : MvPowerSeries.coeff n G = 0
  · by_cases h2 : MvPowerSeries.coeff n H = 0
    · exact absurd (by simp [h1, h2]) hn
    · exact hH n h2
  · exact hG n h1

theorem suppOK_Gser {p : ℕ} (hp : 2 ≤ p) (c c' : K) : SuppOK p (Gser p c c') := by
  exact suppOK_C_mul_sub_C_mul (support_ok_a_zero_one hp) (support_ok_a_one_zero hp) c c'

theorem swap_two_a_series (p : ℕ) (x y : Fin 2) (hx : Equiv.swap (0 : Fin 2) 1 x = y)
    (hy : Equiv.swap (0 : Fin 2) 1 y = x) : swap2 (AA K p x y) = AA K p y x := by
  ext n
  rw [Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.coeff_swap2]
  have h1 : (Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.sw n) x = n y := by
    show n ((Equiv.swap (0 : Fin 2) 1).symm x) = n y
    rw [Equiv.symm_swap, hx]
  have h2 : (Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.sw n) y = n x := by
    show n ((Equiv.swap (0 : Fin 2) 1).symm y) = n x
    rw [Equiv.symm_swap, hy]
  show AA K p x y (Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.sw n) = AA K p y x n
  simp only [AA, h1, h2]

theorem swap_two_g_series (p : ℕ) (c c' : K) : swap2 (Gser p c c') = Gser p (-c') (-c) := by
  have hA : swap2 (AA K p 0 1) = AA K p 1 0 := swap_two_a_series p 0 1 (by simp) (by simp)
  have hB : swap2 (AA K p 1 0) = AA K p 0 1 := swap_two_a_series p 1 0 (by simp) (by simp)
  have eA : Aser K p = AA K p 0 1 := rfl
  have eB : Aser' K p = AA K p 1 0 := rfl
  ext n
  rw [Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.coeff_swap2]
  simp only [Gser, eA, eB, map_sub, MvPowerSeries.coeff_C_mul]
  rw [← Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.coeff_swap2, ← Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.coeff_swap2, hA, hB]
  ring

private theorem coeff_subst_C_mul_X_eq_mul_coeff (a : Fin 2 → K) (G : MvPowerSeries (Fin 2) K)
    (n : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff n
        (MvPowerSeries.subst (fun s => MvPowerSeries.C (a s) * MvPowerSeries.X s) G) =
      (a 0 ^ n 0 * a 1 ^ n 1) * MvPowerSeries.coeff n G := by
  have e : (fun s => MvPowerSeries.C (a s) * (MvPowerSeries.X s : MvPowerSeries (Fin 2) K)) =
      a • MvPowerSeries.X := by
    funext s
    simp [MvPowerSeries.smul_eq_C_mul]
  rw [e, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale,
    Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]

theorem scale_of_suppOK {p : ℕ} {G : MvPowerSeries (Fin 2) K} (hG : SuppOK p G) {ζ : K}
    (hζ : ζ ^ (p ^ 2 - 1) = 1) :
    MvPowerSeries.subst ![MvPowerSeries.C ζ * (MvPowerSeries.X 0 :
        MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] G =
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1] G := by
  have eL : ![MvPowerSeries.C ζ * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1] = fun s => MvPowerSeries.C (![ζ, 1] s) * MvPowerSeries.X s := by
    funext s; fin_cases s <;> simp
  have eR : ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.C (ζ ^ p) * MvPowerSeries.X 1] =
      fun s => MvPowerSeries.C (![1, ζ ^ p] s) * MvPowerSeries.X s := by
    funext s; fin_cases s <;> simp
  rw [eL, eR]
  ext n
  rw [coeff_subst_C_mul_X_eq_mul_coeff, coeff_subst_C_mul_X_eq_mul_coeff]
  by_cases h : MvPowerSeries.coeff n G = 0
  · simp [h]
  · obtain ⟨-, -, hmod⟩ := hG n h
    have hmod' : n 0 % (p ^ 2 - 1) = (p * n 1) % (p ^ 2 - 1) := hmod
    have key : ζ ^ n 0 = (ζ ^ p) ^ n 1 := by
      rw [← pow_mul, pow_eq_pow_mod (n 0) hζ, pow_eq_pow_mod (p * n 1) hζ, hmod']
    simp [key]

theorem constant_coeff_partial_coboundary {F G : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hG0 : MvPowerSeries.constantCoeff G = 0) :
    MvPowerSeries.constantCoeff (d1 F G) = 0 := by
  have hin : MvPowerSeries.constantCoeff (in3 F) = 0 := by
    show MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] F) = 0
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero F, hF0]
    intro i; fin_cases i <;> simp
  have e1 : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![in3 F, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] G) = 0 := by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero G, hG0]
    intro i; fin_cases i <;> simp [hin]
  have e2 : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] G) = 0 := by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero G, hG0]
    intro i; fin_cases i <;> simp
  have e3 : MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] G) = 0 := by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero G, hG0]
    intro i; fin_cases i <;> simp
  show MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![in3 F, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] G -
    MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] G -
    MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] G) = 0
  rw [map_sub, map_sub, e1, e2, e3]
  simp

theorem DeS_Gser {p : ℕ} (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) (σ : K →+* K) {c : K}
    (hσσ : σ (σ c) = c) :
    DeS p σ (Gser p c (σ c)) =
      MvPowerSeries.C (σ c) * (at1 0 (g0F K p) * at1 1 (lgF K p)) -
        MvPowerSeries.C c * (at1 0 (lgF K p) * at1 1 (g0F K p)) := by
  unfold DeS
  rw [Formalism.InvariantFactorPaths.G7.CoboundarySeries.map_Gser σ p c (σ c), hσσ, Formalism.InvariantFactorPaths.G7.Top.frobExprG K p c (σ c) hp hpK,
    ← mul_assoc, ← map_mul, inv_mul_cancel₀ hpK, map_one, one_mul]

theorem partial_coboundary_de_s_g_series {p : ℕ} (hp : 2 ≤ p) (hpK : (p : K) ≠ 0) (σ : K →+* K) {c : K}
    (hσσ : σ (σ c) = c) {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hl : cob F (lgF K p) = 0) :
    d1 F (DeS p σ (Gser p c (σ c))) =
      MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * at1 2 (lgF K p)) := by
  have hH : Hser p σ (Gser p c (σ c)) (σ c) (-c) = 0 := by
    unfold Hser
    rw [DeS_Gser hp hpK σ hσσ, map_neg]
    ring
  have h0 : d1 F (0 : MvPowerSeries (Fin 2) K) = 0 := by
    have h := Formalism.InvariantFactorPaths.G7.TwoVariableSwapLemmas.partial_coboundary_C_mul hF0 (0 : K) 0
    simpa using h
  have h := Formalism.InvariantFactorPaths.G7.CoboundarySeries.partial_coboundary_h_series (p := p) σ hF0 hl (Gser p c (σ c)) (σ c) (-c)
  rw [hH, h0] at h
  exact sub_eq_zero.mp h.symm

end Supp

theorem derivIs_Gser {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {p : ℕ}
    (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹) {c c' : K} (hc : ‖c‖ ≤ 1) (hc' : ‖c'‖ ≤ 1) :
    DerivIs p (Gser p c c') c := by
  obtain ⟨h1, h2⟩ := Formalism.InvariantFactorPaths.G7.Top.derivA K p hp hnp
  have e : MvPowerSeries.pderiv (R := K) 0 (Gser p c c') -
      MvPowerSeries.C c * (at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (g0F K p)) =
      c • (MvPowerSeries.pderiv (R := K) 0 (Aser K p) -
        at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (g0F K p)) -
      c' • MvPowerSeries.pderiv (R := K) 0 (Aser' K p) := by
    unfold Gser
    rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul,
      map_sub, Derivation.map_smul, Derivation.map_smul, smul_sub]
    abel
  unfold DerivIs
  rw [e]
  intro n
  rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    exact mul_le_one₀ hc (norm_nonneg _) (h1 n)
  · rw [norm_neg, norm_mul]
    exact mul_le_one₀ hc' (norm_nonneg _) (h2 n)

theorem frobenius_partial_coboundary_bound {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {p : ℕ}
    {σ : K →+* K} (hU : UnrOK K p σ) {F : MvPowerSeries (Fin 2) K} (hF : IsLawOfLog p F)
    {G : MvPowerSeries (Fin 2) K} {c : K} (hc : ‖c‖ ≤ 1) (hDer : DerivIs p G c)
    (hΔ : d1 F (DeS p σ G) =
      MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * at1 2 (lgF K p))) :
    Bd (p : ℝ)⁻¹ (frobVar p (MvPowerSeries.map σ (d1 F G)) -
      MvPowerSeries.C (p : K) * d1 F G) := by
  obtain ⟨hp, -, hnp, -, hσ⟩ := hU
  have hσF : MvPowerSeries.map σ F = F := (Top.lawSymm K p hp hnp F hF).1 σ
  have hδi : Integral (cob F (g0F K p)) := Top.deIntegral K p σ hp hnp hσ F hF
  obtain ⟨hF0, hFi, hFc⟩ := hF
  have hp0 : p ≠ 0 := hp.ne_zero
  have hp2 : 2 ≤ p := hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnp
    exact (inv_pos.mpr hppos).ne hnp
  have hinv : ‖((p : K)⁻¹)‖ = (p : ℝ) := by rw [norm_inv, hnp, inv_inv]
  have hscale : ∀ f : MvPowerSeries (Fin 3) K, Bd (p : ℝ)⁻¹ f →
      Integral (MvPowerSeries.C ((p : K)⁻¹) * f) := by
    intro f hf n
    rw [MvPowerSeries.coeff_C_mul, norm_mul, hinv]
    calc (p : ℝ) * ‖MvPowerSeries.coeff n f‖ ≤ (p : ℝ) * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left (hf n) hppos.le
      _ = 1 := mul_inv_cancel₀ hppos.ne'

  have hX0 : ∀ i : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) = 0 :=
    fun i => by simp
  have hXp0 : ∀ i : Fin 3,
      MvPowerSeries.constantCoeff ((MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ^ p) = 0 :=
    fun i => by simp [hp0]
  have hsX : ∀ i : Fin 3, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) :=
    fun i => PowerSeries.HasSubst.X i

  have hin3 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] :=
    hasSubst_pair (hX0 0) (hX0 1)
  have hin3c : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] i) = 0 :=
    fun i => by fin_cases i <;> simp
  have hin3i : ∀ i : Fin 2, Integral
      (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] i) := fun i => by
    fin_cases i
    · exact integral_X 0
    · exact integral_X 1
  have hA0 : MvPowerSeries.constantCoeff (in3 F) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hin3 hin3c hF0
  have hAi : Integral (in3 F) := LogarithmEquivalence.integral_subst' hin3c hin3i hFi
  have hδ3i : Integral (in3 (cob F (g0F K p))) := LogarithmEquivalence.integral_subst' hin3c hin3i hδi
  have hσA : MvPowerSeries.map σ (in3 F) = in3 F := by
    unfold in3
    rw [map_pair σ hin3, hσF, MvPowerSeries.map_X, MvPowerSeries.map_X]
  have hsA : PowerSeries.HasSubst (in3 F) := PowerSeries.HasSubst.of_constantCoeff_zero hA0
  have hAp0 : MvPowerSeries.constantCoeff (in3 F ^ p) = 0 := by
    rw [map_pow, hA0, zero_pow hp0]
  have hfA0 : MvPowerSeries.constantCoeff (frobVar p (in3 F)) = 0 := by
    rw [constantCoeff_frobVar hp0, hA0]

  set r : MvPowerSeries (Fin 3) K :=
    MvPowerSeries.C ((p : K)⁻¹) * (frobVar p (in3 F) - in3 F ^ p) with hr
  have hCC : MvPowerSeries.C (p : K) * MvPowerSeries.C ((p : K)⁻¹) =
      (1 : MvPowerSeries (Fin 3) K) := by
    rw [← map_mul, mul_inv_cancel₀ hpK, map_one]
  have hFr : frobVar p (in3 F) = in3 F ^ p + MvPowerSeries.C (p : K) * r := by
    rw [hr, ← mul_assoc, hCC]
    ring
  have hri : Integral r := by
    refine hscale _ fun n => ?_
    have h := frob_congr (σ := σ) hp hnp hσ (f := in3 F) hAi n
    rw [PhiH_apply, hσA, map_sub, norm_sub_rev, ← map_sub] at h
    exact h
  have hr0 : MvPowerSeries.constantCoeff r = 0 := by
    rw [hr, map_mul, map_sub, hfA0, hAp0, sub_zero, mul_zero]

  have h1 : MvPowerSeries.HasSubst ![in3 F, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K)] :=
    hasSubst_pair hA0 (hX0 2)
  have h2 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] :=
    hasSubst_pair (hX0 0) (hX0 2)
  have h3 : MvPowerSeries.HasSubst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] :=
    hasSubst_pair (hX0 1) (hX0 2)
  set Gs : MvPowerSeries (Fin 2) K := MvPowerSeries.map σ G with hGs
  have hd1P : d1 F (frobVar p Gs) =
      MvPowerSeries.subst ![in3 F ^ p, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Gs -
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ^ p,
        MvPowerSeries.X 2 ^ p] Gs -
      MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) ^ p,
        MvPowerSeries.X 2 ^ p] Gs := by
    unfold d1
    rw [pair_frobVar hp0 h1, pair_frobVar hp0 h2, pair_frobVar hp0 h3]
  have hd1s : frobVar p (MvPowerSeries.map σ (d1 F G)) =
      MvPowerSeries.subst ![frobVar p (in3 F),
        (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Gs -
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ^ p,
        MvPowerSeries.X 2 ^ p] Gs -
      MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) ^ p,
        MvPowerSeries.X 2 ^ p] Gs := by
    unfold d1
    rw [map_sub, map_sub, map_pair σ h1, map_pair σ h2, map_pair σ h3, hσA, MvPowerSeries.map_X,
      MvPowerSeries.map_X, MvPowerSeries.map_X, frobVar_sub hp0, frobVar_sub hp0,
      frobVar_pair hp0 h1, frobVar_pair hp0 h2, frobVar_pair hp0 h3, frobVar_X hp0, frobVar_X hp0,
      frobVar_X hp0]

  set Φ : MvPowerSeries (Fin 2) K :=
    Gs - MvPowerSeries.C (σ c) * (at1 0 (lgF K p) * at1 1 (g0F K p)) with hΦ
  have hΦi : Integral (MvPowerSeries.pderiv (R := K) 0 Φ) := by
    have e : MvPowerSeries.pderiv (R := K) 0 Φ = MvPowerSeries.map σ
        (MvPowerSeries.pderiv (R := K) 0 G -
          MvPowerSeries.C c * (at1 0 (PowerSeries.derivative K (lgF K p)) * at1 1 (g0F K p))) := by
      rw [hΦ, map_sub, pderiv_prod, map_sub, map_mul, map_mul, MvPowerSeries.map_C, map_inVar,
        map_inVar, map_derivative, map_lgF, map_g0F, map_pderiv]
    rw [e]
    intro n
    rw [MvPowerSeries.coeff_map]
    exact norm_sigma_le hσ hp.one_le (hDer n)
  have hE1 := Top.divDeriv K (Fin 2) (Fin 3) p hp hnp 0 Φ
    ![in3 F ^ p, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] r hΦi
    (fun i => by
      fin_cases i
      · exact hAp0
      · exact hXp0 2)
    (fun i => by
      fin_cases i
      · exact int_pow hAi p
      · exact int_pow (integral_X 2) p) hr0 hri
  have hupd : Function.update ![in3 F ^ p, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] 0
      (![in3 F ^ p, (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] 0 +
        MvPowerSeries.C (p : K) * r) =
      ![frobVar p (in3 F), (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] := by
    funext i
    fin_cases i
    · simp [hFr]
    · simp
  rw [hupd] at hE1
  have hSΦ : ∀ u v : MvPowerSeries (Fin 3) K, MvPowerSeries.HasSubst ![u, v] →
      MvPowerSeries.subst ![u, v] Φ = MvPowerSeries.subst ![u, v] Gs -
        MvPowerSeries.C (σ c) *
          (PowerSeries.subst u (lgF K p) * PowerSeries.subst v (g0F K p)) := by
    intro u v h
    rw [hΦ, MvPowerSeries.subst_sub h, MvPowerSeries.subst_mul h, MvPowerSeries.subst_mul h,
      MvPowerSeries.subst_C, subst_single_var h, subst_single_var h]
    rfl

  have hlog : PowerSeries.subst F (lgF K p) = at1 0 (lgF K p) + at1 1 (lgF K p) := by
    unfold cob at hFc
    linear_combination hFc
  have hsF : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF0
  have hlogA : PowerSeries.subst (in3 F) (lgF K p) =
      (at1 0 (lgF K p) + at1 1 (lgF K p) : MvPowerSeries (Fin 3) K) := by
    have h := congrArg in3 hlog
    unfold in3 at h ⊢
    rw [subst_psubst hin3 hsF, MvPowerSeries.subst_add hin3, subst_single_var hin3, subst_single_var hin3] at h
    exact h
  have hat : ∀ i : Fin 3, at1 i (g0F K p) =
      MvPowerSeries.C ((p : K)⁻¹) * frobVar p (at1 i (lgF K p)) := fun i => by
    unfold at1
    rw [subst_g_zero_eq_log hp2 hpK (hsX i), frobVar_psubst hp0 (hsX i), frobVar_X hp0]
  have hδ : in3 (cob F (g0F K p)) = MvPowerSeries.C ((p : K)⁻¹) *
      (PowerSeries.subst (in3 F ^ p) (lgF K p) -
        PowerSeries.subst (frobVar p (in3 F)) (lgF K p)) := by
    have e : in3 (cob F (g0F K p)) =
        PowerSeries.subst (in3 F) (g0F K p) - at1 0 (g0F K p) - at1 1 (g0F K p) := by
      unfold cob in3
      rw [MvPowerSeries.subst_sub hin3, MvPowerSeries.subst_sub hin3, subst_psubst hin3 hsF,
        subst_single_var hin3, subst_single_var hin3]
      rfl
    rw [e, subst_g_zero_eq_log hp2 hpK hsA, hat, hat, ← frobVar_psubst hp0 hsA, hlogA, frobVar_add hp0]
    ring
  have hgb : PowerSeries.subst ((MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p) (g0F K p) =
      at1 2 (lgF K p) - MvPowerSeries.X 2 := subst_pow_g_zero hp2 hpK (hsX 2)

  have key : d1 F (DeS p σ G) -
      MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * at1 2 (lgF K p)) =
      MvPowerSeries.C ((p : K)⁻¹) *
        ((frobVar p (MvPowerSeries.map σ (d1 F G)) - MvPowerSeries.C (p : K) * d1 F G) -
          (MvPowerSeries.subst ![frobVar p (in3 F),
              (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ -
            MvPowerSeries.subst ![in3 F ^ p,
              (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ)) -
        MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * MvPowerSeries.X 2) := by
    unfold DeS
    rw [partial_coboundary_linear hF0, hd1P, hd1s, hSΦ _ _ (hasSubst_pair hfA0 (hXp0 2)),
      hSΦ _ _ (hasSubst_pair hAp0 (hXp0 2)), hgb, hδ]
    ring
  have fin : frobVar p (MvPowerSeries.map σ (d1 F G)) - MvPowerSeries.C (p : K) * d1 F G =
      (MvPowerSeries.subst ![frobVar p (in3 F),
          (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ -
        MvPowerSeries.subst ![in3 F ^ p,
          (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ) +
      MvPowerSeries.C (p : K) *
        (MvPowerSeries.C (σ c) * (in3 (cob F (g0F K p)) * MvPowerSeries.X 2)) := by
    linear_combination (-(MvPowerSeries.C (p : K))) * key + MvPowerSeries.C (p : K) * hΔ -
      ((frobVar p (MvPowerSeries.map σ (d1 F G)) - MvPowerSeries.C (p : K) * d1 F G) -
          (MvPowerSeries.subst ![frobVar p (in3 F),
              (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ -
            MvPowerSeries.subst ![in3 F ^ p,
              (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) K) ^ p] Φ)) * hCC
  rw [fin]
  refine bd_add hE1 ?_
  have hb := bd_mul (inv_nonneg.mpr hppos.le) zero_le_one
    (bd_C (ι := Fin 3) (inv_nonneg.mpr hppos.le) hnp.le)
    (int_mul (bd_C zero_le_one (norm_sigma_le hσ hp.one_le hc)) (int_mul hδ3i (integral_X 2)))
  rwa [mul_one] at hb

theorem partial_coboundary_g_series_equiv {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K] {p : ℕ}
    {σ : K →+* K} (hU : UnrOK K p σ) {F : MvPowerSeries (Fin 2) K} (hF : IsLawOfLog p F)
    {c : K} (hc : ‖c‖ ≤ 1) (hσσ : σ (σ c) = c) : Simeq (d1 F (Gser p c (σ c))) 0 := by
  have hp2 : 2 ≤ p := le_of_lt hU.2.1
  have hpK : (p : K) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hσc : ‖σ c‖ ≤ 1 := by
    have h1 : ‖σ c - c ^ p‖ ≤ (p : ℝ)⁻¹ := hU.2.2.2.2 c hc
    have h2 : ‖c ^ p‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc
    have h3 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ p))
    calc ‖σ c‖ = ‖(σ c - c ^ p) + c ^ p‖ := by rw [sub_add_cancel]
      _ ≤ max ‖σ c - c ^ p‖ ‖c ^ p‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (h1.trans h3) h2
  have hG0 : MvPowerSeries.constantCoeff (Gser p c (σ c)) = 0 := by
    by_contra h
    have h' : MvPowerSeries.coeff 0 (Gser p c (σ c)) ≠ 0 := by
      rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    obtain ⟨h1, -, -⟩ := suppOK_Gser hp2 c (σ c) 0 h'
    simp at h1
  have hd0 : MvPowerSeries.constantCoeff (d1 F (Gser p c (σ c))) = 0 := constant_coeff_partial_coboundary hF.1 hG0
  refine ⟨by rw [sub_zero]; exact hd0, ?_⟩
  rw [sub_zero]
  have hDer := derivIs_Gser (K := K) hU.1 hU.2.2.1 hc hσc
  have hΔ := partial_coboundary_de_s_g_series hp2 hpK σ hσσ hF.1 hF.2.2
  have hB := frobenius_partial_coboundary_bound hU hF hc hDer hΔ
  exact (Formalism.InvariantFactorPaths.G7.Top.dworkMv K (Fin 3) p σ hU.1 hU.2.2.1 hU.2.2.2.2 _ hd0).mpr hB

end CoefficientSupportCongruences

open CoefficientSupportCongruences in
theorem g_c_is_beta : GcIsBeta := by
  intro K _ _ _ p σ hU F hF c hc hσσ
  have hp2 : 2 ≤ p := le_of_lt hU.2.1
  have hσc : ‖σ c‖ ≤ 1 := by
    have h1 : ‖σ c - c ^ p‖ ≤ (p : ℝ)⁻¹ := hU.2.2.2.2 c hc
    have h2 : ‖c ^ p‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc
    have h3 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ p))
    calc ‖σ c‖ = ‖(σ c - c ^ p) + c ^ p‖ := by rw [sub_add_cancel]
      _ ≤ max ‖σ c - c ^ p‖ ‖c ^ p‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ 1 := max_le (h1.trans h3) h2
  have hS := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Fin 2)).1
  refine ⟨?_, partial_coboundary_g_series_equiv hU hF hc hσσ, ?_, ?_⟩
  · intro n hn
    by_contra h
    obtain ⟨h0, h1, -⟩ := suppOK_Gser (K := K) hp2 c (σ c) n h
    omega
  · rw [swap_two_g_series]
    have h := partial_coboundary_g_series_equiv hU hF (c := -σ c) (by rwa [norm_neg]) (by simp [hσσ])
    simpa [hσσ] using h
  · intro ζ hζ
    rw [scale_of_suppOK (suppOK_Gser hp2 c (σ c)) hζ]
    exact hS _

end Formalism.InvariantFactorPaths.G7
