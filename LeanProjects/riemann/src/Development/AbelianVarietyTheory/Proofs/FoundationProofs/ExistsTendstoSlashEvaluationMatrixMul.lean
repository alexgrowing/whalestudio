import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashQExpansionCoeffWidthTransformStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEqZeroOfSumPlusMinusRepsEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashSubQExpansionPartialSumIsBigOStatement

noncomputable section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem tendsto_inv_qParam_pow_mul {M a : ℕ} (ha : a < M) {g : ℍ → ℂ}
    (hg : g =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im)) :
    Tendsto (fun τ : ℍ => (Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ a)⁻¹ * g τ) atImInfty (𝓝 0) := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_le a).trans_lt ha
  have haM : (a : ℝ) < M := by exact_mod_cast ha
  have h1 : (fun τ : ℍ => (Function.Periodic.qParam (M : ℝ) (τ : ℂ) ^ a)⁻¹) =O[atImInfty]
      fun τ : ℍ => Real.exp (2 * Real.pi * τ.im * a / M) := by
    refine Asymptotics.IsBigO.of_norm_le fun τ => le_of_eq ?_
    rw [norm_inv, norm_pow, Function.Periodic.norm_qParam, ← Real.exp_nat_mul, ← Real.exp_neg, coe_im]
    congr 1; ring
  refine (h1.mul hg).trans_tendsto ?_
  have hr : -2 * Real.pi * (1 - a / M) < 0 := by
    have : (a : ℝ) / M < 1 := (div_lt_one hM).2 haM
    have := Real.pi_pos
    nlinarith
  have h2 : Tendsto (fun τ : ℍ => τ.im) atImInfty atTop := tendsto_comap
  refine (Real.tendsto_exp_atBot.comp (h2.const_mul_atTop_of_neg hr)).congr fun τ => ?_
  simp only [Function.comp_apply]
  rw [← Real.exp_add]; congr 1; ring

theorem sum_mul_co_eq {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {r : ℕ} {s : Fin r → SL(2, ℤ)} {w : Fin r → ℤ}
    {F : Fin r → ℍ → ℂ} (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (l : Fin r) {a : ℕ} (ha : a < M) (c : Fin r → ℂ)
    (hc : ∀ i, (leadM M s w F).mulVec c i = co M (w l) (F l) (s i) a) (x : SL(2, ℤ)) {n : ℕ} (hn : n < M) :
    ∑ j, c j * co M (w j) (F j) x n = if n = a then co M (w l) (F l) x a else 0 := by
  have H := fun j => GlobalTheory.T.slashQExpansionCoeffWidth_transform M Γ (w j) (F j) hM hΓ (hF j).2
  rw [← sub_eq_zero]
  refine GlobalTheory.T.coeff_eq_zero_of_sum_plusMinusReps_eq_zero M Γ r s
    (fun x n => ∑ j, c j * co M (w j) (F j) x n - if n = a then co M (w l) (F l) x a else 0)
    hM hs ?_ ?_ ?_ ?_ x n hn
  · intro x n
    simp only [fun j => (H j).1, mul_sub, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · split_ifs with h
      · rw [h]
      · simp
  · intro γ hγ x n
    simp only [fun j => (H j).2.1 γ hγ]
  · intro x n
    simp only [fun j => (H j).2.2 (hF j).1, mul_neg, Finset.sum_neg_distrib]
    split_ifs <;> ring
  · intro i
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' (Finset.range M) a, if_pos (Finset.mem_range.2 ha),
      ← hc i, Finset.sum_comm, sub_eq_zero]
    simp only [Matrix.mulVec, dotProduct, leadM, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [← Finset.mul_sum, mul_comm]

theorem exists_tendsto_evM_mul (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (hM : 0 < M) (hΓ : CongruenceSubgroup.Gamma M ≤ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hdet : (leadM M s w F).det ≠ 0) :
    ∃ U : ℍ → Matrix (Fin r) (Fin r) ℂ,
      Tendsto (fun τ => evM s w F τ * U τ) atImInfty (𝓝 (leadM M s w F)) ∧
        Tendsto (fun τ => ModularForm.discriminant τ • U τ) atImInfty (𝓝 0) := by
  set c : Fin r → ℕ → Fin r → ℂ := fun l a =>
    (leadM M s w F)⁻¹.mulVec fun i => co M (w l) (F l) (s i) a with hcdef
  have hc : ∀ l a i, (leadM M s w F).mulVec (c l a) i = co M (w l) (F l) (s i) a := by
    intro l a i
    simp only [hcdef]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), Matrix.one_mulVec]
  set t : ℍ → ℂ := fun τ => Function.Periodic.qParam (M : ℝ) (τ : ℂ) with ht
  have ht0 : ∀ τ, t τ ≠ 0 := fun τ => Complex.exp_ne_zero _
  refine ⟨fun τ => Matrix.of fun j l => ∑ a ∈ Finset.range M, c l a j * (t τ ^ a)⁻¹, ?_, ?_⟩
  · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun l => ?_
    have hlim : Tendsto (fun τ : ℍ => leadM M s w F i l + ∑ a ∈ Finset.range M, ∑ j, c l a j *
        ((t τ ^ a)⁻¹ * ((F j ∣[w j] s i) τ -
          ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n * t τ ^ n))) atImInfty
        (𝓝 (leadM M s w F i l + ∑ a ∈ Finset.range M, ∑ j, c l a j * 0)) := by
      refine tendsto_const_nhds.add (tendsto_finsetSum _ fun a ha => tendsto_finsetSum _ fun j _ => ?_)
      exact (tendsto_inv_qParam_pow_mul (Finset.mem_range.1 ha)
        (GlobalTheory.T.slash_sub_qExpansion_partialSum_isBigO M Γ (w j) (F j) hM hΓ (hF j).2 (s i))).const_mul _
    simp only [mul_zero, Finset.sum_const_zero, add_zero] at hlim
    refine hlim.congr fun τ => ?_
    simp only [Matrix.mul_apply, evM, leadM, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_range.1 ha
    have key : ∑ j, c l a j * ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n * t τ ^ n =
        co M (w l) (F l) (s i) a * t τ ^ a := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      have : ∀ n ∈ Finset.range M, ∑ j, c l a j * (co M (w j) (F j) (s i) n * t τ ^ n) =
          if n = a then co M (w l) (F l) (s i) a * t τ ^ a else 0 := by
        intro n hn
        simp only [← mul_assoc, ← Finset.sum_mul]
        rw [sum_mul_co_eq hM hΓ hs hF l ha' (c l a) (hc l a) (s i) (Finset.mem_range.1 hn)]
        split_ifs with h
        · rw [h]
        · simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.range M) a, if_pos ha]
    have hta : t τ ^ a ≠ 0 := pow_ne_zero _ (ht0 τ)
    have e : co M (w l) (F l) (s i) a =
        ∑ j, (t τ ^ a)⁻¹ * (c l a j * ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n * t τ ^ n) := by
      rw [← Finset.mul_sum, key]; field_simp
    rw [e, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  · refine tendsto_pi_nhds.2 fun j => tendsto_pi_nhds.2 fun l => ?_
    have hΔ : ModularForm.discriminant =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
      simpa [CuspForm.coe_discriminant] using
        CuspFormClass.exp_decay_atImInfty CuspForm.discriminant one_pos one_mem_strictPeriods_SL
    have hlim : Tendsto (fun τ : ℍ => ∑ a ∈ Finset.range M, c l a j *
        ((t τ ^ a)⁻¹ * ModularForm.discriminant τ)) atImInfty (𝓝 (∑ a ∈ Finset.range M, c l a j * 0)) :=
      tendsto_finsetSum _ fun a ha =>
        (tendsto_inv_qParam_pow_mul (Finset.mem_range.1 ha) hΔ).const_mul _
    simp only [mul_zero, Finset.sum_const_zero] at hlim
    refine hlim.congr fun τ => ?_
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.OddFrame
