import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.ExcOne
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.ExcTerm
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.EffBase

open Formalism.ZeroFreeDirichlet

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

theorem charSum_lowerOf (q a : ℕ) [NeZero q] (ha : Nat.Coprime a q) (x K : ℝ) (hx : 0 ≤ x)
    (B : DirichletCharacter ℂ q → Finset ℝ) (hB : ∀ χ, ∀ β ∈ B χ, 0 ≤ β)
    (hE : ∀ χ, ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) +
      ∑ β ∈ B χ, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ K) :
    x - ∑ χ : DirichletCharacter ℂ q, ∑ β ∈ B χ, x ^ β / β - (q.totient : ℝ) * K ≤
      (q.totient : ℝ) * psiAP q a x := by
  set S : DirichletCharacter ℂ q → ℝ := fun χ => ∑ β ∈ B χ, x ^ β / β with hS
  set E : DirichletCharacter ℂ q → ℂ := fun χ => psiChi χ x - (if χ = 1 then (x : ℂ) else 0) +
      ∑ β ∈ B χ, (x : ℂ) ^ (β : ℂ) / (β : ℂ) with hEdef
  have hSnn : ∀ χ, 0 ≤ S χ := fun χ =>
    Finset.sum_nonneg (fun β hβ => div_nonneg (Real.rpow_nonneg hx β) (hB χ β hβ))
  have hT : ∀ χ, ∑ β ∈ B χ, (x : ℂ) ^ (β : ℂ) / (β : ℂ) = ((S χ : ℝ) : ℂ) := by
    intro χ
    simp only [hS, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun β _ => excTerm_ofReal x β hx)
  have hsplit : ∀ χ, psiChi χ x = (if χ = 1 then (x : ℂ) else 0) + (E χ - ((S χ : ℝ) : ℂ)) := by
    intro χ
    simp only [hEdef, hT]
    ring
  set W : ℂ := ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * (E χ - ((S χ : ℝ) : ℂ)) with hW
  have hid : (((q.totient : ℝ) * psiAP q a x : ℝ) : ℂ) = (x : ℂ) + W := by
    have h0 := chebyshev_progression_orthogonality q a ha x
    simp only [hsplit, mul_add, Finset.sum_add_distrib, principal_character_orthogonality_term q a ha x] at h0
    push_cast
    rw [h0]
  have hre : (q.totient : ℝ) * psiAP q a x = x + W.re := by
    have := congrArg Complex.re hid
    simpa using this
  have hWn : ‖W‖ ≤ (q.totient : ℝ) * K + ∑ χ : DirichletCharacter ℂ q, S χ := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)),
        ‖χ ((a : ZMod q)⁻¹) * (E χ - ((S χ : ℝ) : ℂ))‖ ≤ K + S χ := by
      intro χ _
      rw [norm_mul]
      have h3 := DirichletCharacter.norm_le_one χ ((a : ZMod q)⁻¹)
      have h4 : ‖E χ - ((S χ : ℝ) : ℂ)‖ ≤ K + S χ := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hSnn χ)]
        have := hE χ
        linarith
      calc ‖χ ((a : ZMod q)⁻¹)‖ * ‖E χ - ((S χ : ℝ) : ℂ)‖ ≤ 1 * ‖E χ - ((S χ : ℝ) : ℂ)‖ := by
            gcongr
        _ ≤ K + S χ := by rw [one_mul]; exact h4
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, card_dirichletCharacter_eq_totient]
  have hreW : -‖W‖ ≤ W.re := by
    have := Complex.abs_re_le_norm W
    linarith [neg_abs_le W.re]
  show x - ∑ χ : DirichletCharacter ℂ q, S χ - (q.totient : ℝ) * K ≤ _
  linarith

theorem excSum_leOf {ι : Type*} [Fintype ι] (B : ι → Finset ℝ) (f : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hcard : ∀ i, (B i).card ≤ 1) (huniq : ∀ i j, (B i).Nonempty → (B j).Nonempty → i = j)
    (hf : ∀ i, ∀ β ∈ B i, f β ≤ M) : ∑ i, ∑ β ∈ B i, f β ≤ M := by
  by_cases h : ∃ i, (B i).Nonempty
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i]
    · have h1 : (B i).card = 1 := le_antisymm (hcard i) (Finset.card_pos.mpr hi)
      obtain ⟨β, hβ⟩ := Finset.card_eq_one.mp h1
      rw [hβ, Finset.sum_singleton]
      exact hf i β (by rw [hβ]; exact Finset.mem_singleton_self β)
    · intro j _ hji
      have : ¬ (B j).Nonempty := fun hj => hji (huniq j i hj hi)
      rw [Finset.not_nonempty_iff_eq_empty.mp this, Finset.sum_empty]
    · intro hi'
      exact absurd (Finset.mem_univ i) hi'
  · have h' : ∀ i, ¬ (B i).Nonempty := fun i hi => h ⟨i, hi⟩
    have : ∑ i, ∑ β ∈ B i, f β = 0 := Finset.sum_eq_zero (fun i _ => by
      rw [Finset.not_nonempty_iff_eq_empty.mp (h' i), Finset.sum_empty])
    rw [this]
    exact hM

theorem psiAPLowerOf (A : ℕ) (hA : ExcBoundAt A) : ∃ c c₀ C : ℝ, 0 < c ∧ 0 < c₀ ∧ 0 ≤ C ∧
    ∀ (m a : ℕ) (x : ℝ), 1 ≤ m → Nat.Coprime a m → 0 < x → 4 ≤ Real.log x →
      (m : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) →
      c₀ * x / (m : ℝ) ^ (A + 1) - C * x * Real.exp (-c * Real.sqrt (Real.log x)) ≤ psiAP m a x := by
  obtain ⟨c₁, hc₁, hc₁', hex⟩ := excOne
  obtain ⟨c, C, hc, hPC⟩ := psiChiBound c₁ hc₁ hc₁'
  obtain ⟨cE, hcE, hEB⟩ := hA
  refine ⟨c, min 1 cE / 2, max C 0, hc, by positivity, le_max_right _ _, ?_⟩
  intro m a x hm ha hx hL hmx
  have : NeZero m := ⟨by omega⟩
  obtain ⟨B, hBexc, hBuniq, hBprop⟩ := hex m
  set e := Real.exp (-c * Real.sqrt (Real.log x)) with he
  set K := max C 0 * x * e with hKdef
  have hx2 : 2 ≤ x := by
    have h1 : (4 : ℝ) + 1 ≤ Real.exp 4 := Real.add_one_le_exp 4
    have h2 : Real.exp 4 ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr hL
    rw [Real.exp_log hx] at h2
    linarith
  have hK : ∀ χ : DirichletCharacter ℂ m, ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) +
      ∑ β ∈ B χ, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ K := by
    intro χ
    refine (hPC m χ (B χ) x (hBexc χ) hx2 hmx).trans ?_
    have : 0 ≤ x * e := by positivity
    rw [hKdef, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  have hB0 : ∀ χ, ∀ β ∈ B χ, 0 ≤ β := fun χ β hβ => by
    have := (hBprop χ β hβ).2.2.1
    linarith
  have hlow := charSum_lowerOf m a ha x K hx.le B hB0 hK
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmA1 : (1 : ℝ) ≤ (m : ℝ) ^ A := one_le_pow₀ hm1
  have hminv : 0 < ((m : ℝ) ^ A)⁻¹ := by positivity
  have hminv1 : ((m : ℝ) ^ A)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hmA1
  set d := min 1 cE * ((m : ℝ) ^ A)⁻¹ / 2 with hd
  have hmin1 : min 1 cE ≤ 1 := min_le_left _ _
  have hminE : min 1 cE ≤ cE := min_le_right _ _
  have hmin0 : 0 < min 1 cE := lt_min one_pos hcE
  have hd1 : d ≤ 1 / 2 := by
    have : min 1 cE * ((m : ℝ) ^ A)⁻¹ ≤ 1 * 1 := mul_le_mul hmin1 hminv1 hminv.le zero_le_one
    rw [hd]; linarith
  have hd0 : 0 < d := by positivity
  have hS : ∑ χ : DirichletCharacter ℂ m, ∑ β ∈ B χ, x ^ β / β ≤ x * (1 - d) := by
    refine excSum_leOf B (fun β => x ^ β / β) (x * (1 - d)) (by nlinarith) (fun χ => (hBexc χ).1)
      hBuniq ?_
    intro χ β hβ
    obtain ⟨hsq, hne, hhalf, hz⟩ := hBprop χ β hβ
    have hb := hEB m χ β hsq hne hz
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast] at hb
    have hce : cE * ((m : ℝ) ^ A)⁻¹ ≥ min 1 cE * ((m : ℝ) ^ A)⁻¹ :=
      mul_le_mul_of_nonneg_right hminE hminv.le
    have hβ1 : β ≤ 1 := by nlinarith
    have h1 := excTerm x β hx hL hhalf hβ1
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_left _ hx.le
    rw [hd]
    linarith
  have hφpos : (0 : ℝ) < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hφle : (m.totient : ℝ) ≤ m := by exact_mod_cast Nat.totient_le m
  have hmain : x * d ≤ (m.totient : ℝ) * (psiAP m a x + K) := by
    rw [mul_add]
    nlinarith
  have hnn : 0 ≤ psiAP m a x + K := by
    have : (m.totient : ℝ) * 0 ≤ (m.totient : ℝ) * (psiAP m a x + K) := by
      rw [mul_zero]; nlinarith [mul_pos hx hd0]
    exact le_of_mul_le_mul_left this hφpos
  have hmain2 : x * d ≤ (m : ℝ) * (psiAP m a x + K) :=
    hmain.trans (mul_le_mul_of_nonneg_right hφle hnn)
  have hm0 : (0 : ℝ) < m := by linarith
  have hgoal : min 1 cE / 2 * x / (m : ℝ) ^ (A + 1) ≤ psiAP m a x + K := by
    rw [div_le_iff₀ (by positivity)]
    have hxd : min 1 cE / 2 * x = (m : ℝ) ^ A * (x * d) := by
      rw [hd]; field_simp
    rw [hxd]
    have := mul_le_mul_of_nonneg_left hmain2 (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ A)
    calc (m : ℝ) ^ A * (x * d) ≤ (m : ℝ) ^ A * ((m : ℝ) * (psiAP m a x + K)) := this
      _ = (psiAP m a x + K) * (m : ℝ) ^ (A + 1) := by ring
  linarith

end Formalism.HermitianLattices.Ext.SupplyAP
