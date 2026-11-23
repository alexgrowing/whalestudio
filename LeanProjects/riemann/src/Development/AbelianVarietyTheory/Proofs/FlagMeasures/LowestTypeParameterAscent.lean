import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

namespace GlobalTheory.SuVPar

open GlobalTheory.DSSU

theorem diag_mem {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) (hθ : ∑ a, θ a = 0) :
    Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ SUset ε := by
  refine ⟨?_, ?_⟩
  · show Formalism.REAL.inUJ ε _
    unfold Formalism.REAL.inUJ Formalism.REAL.Jm
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    have h1 : star (Complex.exp ((θ a : ℂ) * Complex.I)) * Complex.exp ((θ a : ℂ) * Complex.I) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp [Complex.conj_ofReal]
    calc star (Complex.exp ((θ a : ℂ) * Complex.I)) * (if ε a = true then 1 else -1) *
          Complex.exp ((θ a : ℂ) * Complex.I)
        = (star (Complex.exp ((θ a : ℂ) * Complex.I)) * Complex.exp ((θ a : ℂ) * Complex.I)) *
            (if ε a = true then 1 else -1) := by ring
      _ = _ := by rw [h1, one_mul]
  · rw [Matrix.det_diagonal, ← Complex.exp_sum, ← Finset.sum_mul]
    have : (∑ a, (θ a : ℂ)) = 0 := by exact_mod_cast hθ
    rw [this, zero_mul, Complex.exp_zero]

theorem one_mem {n : ℕ} (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
  have h := diag_mem ε (fun _ => 0) (by simp)
  simpa using h

theorem rho_diff {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (hinj : Function.Injective lam) (a : Fin n) :
    ∃ k : ℤ, rhoNh ε lam a - rhoCh ε lam a = ((n : ℝ) - 1) / 2 - k := by
  set A := (univ.filter fun b => lam b < lam a ∧ ε b ≠ ε a).card
  set B := (univ.filter fun b => lam a < lam b ∧ ε b ≠ ε a).card
  set C := (univ.filter fun b => lam b < lam a ∧ ε b = ε a).card
  set D := (univ.filter fun b => lam a < lam b ∧ ε b = ε a).card
  have key : (A : ℝ) + B + C + D = n - 1 := by
    simp only [A, B, C, D, Finset.card_filter]
    push_cast
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have hpt : ∀ b : Fin n, ((if lam b < lam a ∧ ε b ≠ ε a then (1:ℝ) else 0) +
        (if lam a < lam b ∧ ε b ≠ ε a then (1:ℝ) else 0) +
        (if lam b < lam a ∧ ε b = ε a then (1:ℝ) else 0) +
        (if lam a < lam b ∧ ε b = ε a then (1:ℝ) else 0)) = 1 - (if a = b then 1 else 0) := by
      intro b
      by_cases hab : a = b
      · subst hab; simp
      · have hne : lam b ≠ lam a := fun h => hab (hinj h).symm
        rcases lt_or_gt_of_ne hne with h | h <;> by_cases he : ε b = ε a <;>
          simp [h, he, hab, not_lt_of_gt h]
    rw [Finset.sum_congr rfl (fun b _ => hpt b), Finset.sum_sub_distrib, Finset.sum_ite_eq]
    simp
  refine ⟨(B + C : ℕ), ?_⟩
  simp only [rhoNh, rhoCh]
  change ((A : ℝ) - B) / 2 - ((C : ℝ) - D) / 2 = _
  push_cast
  linarith

theorem wt_int {n : ℕ} (hn : 1 ≤ n) (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hE : Ext ε m π' π)
    (Λ : Fin n → ℝ) (hΛ : ∑ a, Λ a = 0) (v : H) (hv : v ≠ 0) (hw : IsWtS π' Λ v) (a : Fin n) :
    ∃ k : ℤ, Λ a + (m : ℝ) / n = k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)

  have h1 : π' 1 v = v := by
    have := hw (fun _ => 0) (by simp)
    simpa using this
  have hπ1 : π 1 = π' 1 := by
    have := hE 1 (by simp) 1 (one_mem ε)
    simpa using this
  set θ : Fin n → ℝ := fun b => (if b = a then 2 * Real.pi else 0) - 2 * Real.pi / n with hθdef
  have hθ : ∑ b, θ b = 0 := by
    simp only [hθdef, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  set z : ℂ := Complex.exp (((2 * Real.pi / n : ℝ) : ℂ) * Complex.I) with hz
  have hz1 : ‖z‖ = 1 := by rw [hz, Complex.norm_exp_ofReal_mul_I]
  have hzg : z • Matrix.diagonal (fun b => Complex.exp ((θ b : ℂ) * Complex.I)) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, smul_eq_mul, hz]
      rw [← Complex.exp_add]
      rw [Complex.exp_eq_one_iff]
      by_cases hia : i = a
      · refine ⟨1, ?_⟩
        simp only [hθdef, hia, if_true]
        push_cast
        ring
      · refine ⟨0, ?_⟩
        simp only [hθdef, hia, if_false]
        push_cast
        ring
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hmain := hE z hz1 _ (diag_mem ε θ hθ)
  rw [hzg, hπ1] at hmain
  have hv2 := congrArg (fun T : H →L[ℂ] H => T v) hmain
  simp only [h1, ContinuousLinearMap.smul_apply, hw θ hθ, smul_smul] at hv2

  have hsum : (∑ b, Λ b * θ b) = 2 * Real.pi * Λ a := by
    simp only [hθdef, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, ← Finset.sum_mul, hΛ, zero_mul, sub_zero]
    ring
  rw [hsum] at hv2
  have hc : z ^ m * Complex.exp (((2 * Real.pi * Λ a : ℝ) : ℂ) * Complex.I) = 1 := by
    by_contra hne
    have : (z ^ m * Complex.exp (((2 * Real.pi * Λ a : ℝ) : ℂ) * Complex.I) - 1) • v = 0 := by
      rw [sub_smul, one_smul, ← hv2, sub_self]
    rcases smul_eq_zero.mp this with h | h
    · exact hne (sub_eq_zero.mp h)
    · exact hv h
  rw [hz, ← Complex.exp_int_mul, ← Complex.exp_add, Complex.exp_eq_one_iff] at hc
  obtain ⟨k, hk⟩ := hc
  refine ⟨k, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : ((Λ a + (m : ℝ) / n : ℝ) : ℂ) = (k : ℂ) := by
    apply mul_right_cancel₀ hpi
    rw [← hk]
    push_cast
    field_simp
    ring
  exact_mod_cast this

end GlobalTheory.SuVPar

namespace GlobalTheory.SuVPar

theorem parS_lifts : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → ∀ lam' : Fin n → ℝ, IsParS lam' → (∃ S : Submodule ℂ H, IsKTypeS ε lam' π' (lowCh ε lam') S) → IsParU (fun a => lam' a + (m : ℝ) / n) ∧ ∑ a, (lam' a + (m : ℝ) / n) = (m : ℝ) := by
  intro n hn ε H _ _ m π' π hE lam' hP hS
  obtain ⟨hsum0, hinj, -⟩ := hP
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a b h
    exact hinj (add_right_cancel h)
  · intro a
    obtain ⟨S, hΛ, -, -, -, ⟨v, -, hv, hw⟩, -⟩ := hS
    obtain ⟨k1, hk1⟩ := wt_int hn ε m π' π hE _ hΛ v hv hw a
    obtain ⟨k2, hk2⟩ := rho_diff ε lam' hinj a
    refine ⟨k1 + k2 - n + 1, ?_⟩
    have hl : lowCh ε lam' a = lam' a + rhoNh ε lam' a - rhoCh ε lam' a := rfl
    push_cast
    linarith
  · rw [Finset.sum_add_distrib, hsum0, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

end GlobalTheory.SuVPar
