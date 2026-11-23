import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SUCentre

lemma card_lt_add_card_gt {n : ℕ} (lam : Fin n → ℝ) (hinj : Function.Injective lam) (a : Fin n) :
    ((univ.filter fun b => lam b < lam a).card : ℝ) + ((univ.filter fun b => lam a < lam b).card : ℝ) + 1 = n := by
  have h1 : (univ.filter fun b => lam b ≠ lam a) = univ.erase a := by
    ext b; simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    exact ⟨fun h e => h (e ▸ rfl), fun h e => h (hinj e)⟩
  have h2 := Finset.card_filter_add_card_filter_not (s := univ.filter fun b => lam b ≠ lam a)
    (fun b => lam b < lam a)
  have h3 : ((univ.filter fun b => lam b ≠ lam a).filter fun b => lam b < lam a) = univ.filter fun b => lam b < lam a := by
    ext b; simp only [mem_filter, mem_univ, true_and]; exact ⟨fun h => h.2, fun h => ⟨h.ne, h⟩⟩
  have h4 : ((univ.filter fun b => lam b ≠ lam a).filter fun b => ¬ lam b < lam a) = univ.filter fun b => lam a < lam b := by
    ext b; simp only [mem_filter, mem_univ, true_and, not_lt]
    exact ⟨fun h => lt_of_le_of_ne h.2 (Ne.symm h.1), fun h => ⟨h.ne', h.le⟩⟩
  rw [h3, h4, h1, Finset.card_erase_of_mem (mem_univ a), Finset.card_univ, Fintype.card_fin] at h2
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (fun h => (h ▸ a).elim0)
  have : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  rw [← h2] at this
  push_cast at this
  linarith

lemma card_split {n : ℕ} (P Q : Fin n → Prop) [DecidablePred P] [DecidablePred Q] :
    ((univ.filter fun b => P b ∧ Q b).card : ℝ) + ((univ.filter fun b => P b ∧ ¬ Q b).card : ℝ) =
      ((univ.filter P).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not (s := univ.filter P) Q
  rw [Finset.filter_filter, Finset.filter_filter] at h
  exact_mod_cast h

lemma lowCh_shift_int {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) (hlam : IsParU lam) (c : ℝ) (a : Fin n) :
    ∃ k : ℤ, lowCh ε (fun b => lam b - c) a = (k : ℝ) - c := by
  obtain ⟨m0, hm0⟩ := hlam.2 a
  have hN : rhoNh ε (fun b => lam b - c) a = rhoNh ε lam a := by
    simp only [rhoNh, sub_lt_sub_iff_right]
  have hC : rhoCh ε (fun b => lam b - c) a = rhoCh ε lam a := by
    simp only [rhoCh, sub_lt_sub_iff_right]
  have hsum := card_lt_add_card_gt lam hlam.1 a
  have s1 := card_split (fun b => lam b < lam a) (fun b => ε b = ε a)
  have s2 := card_split (fun b => lam a < lam b) (fun b => ε b = ε a)
  refine ⟨m0 + ((univ.filter fun b => lam b < lam a ∧ ε b ≠ ε a).card : ℤ)
    + ((univ.filter fun b => lam a < lam b ∧ ε b = ε a).card : ℤ), ?_⟩
  have e : lowCh ε (fun b => lam b - c) a
      = lam a - c + rhoNh ε (fun b => lam b - c) a - rhoCh ε (fun b => lam b - c) a := rfl
  rw [e, hN, hC]
  simp only [rhoNh, rhoCh]
  push_cast
  simp only [ne_eq] at *
  linarith

lemma scalar_as_torus {n : ℕ} (a0 : Fin n) (z : ℂ) (hz : z ^ n = 1) :
    ∃ t : ℝ, Complex.exp ((t : ℂ) * Complex.I) = z ∧
      ∑ a, (if a = a0 then t - n * t else t) = 0 ∧
      z • (1 : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal (fun a => Complex.exp ((((if a = a0 then t - n * t else t : ℝ)) : ℂ) * Complex.I)) := by
  have hn : n ≠ 0 := fun h => (h ▸ a0).elim0
  have hnorm : ‖z‖ = 1 := by
    have := congrArg norm hz
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn).mp this
  set t := Complex.arg z
  have ht : Complex.exp ((t : ℂ) * Complex.I) = z := by
    have := Complex.norm_mul_exp_arg_mul_I z
    rw [hnorm] at this; simpa using this
  have ht' : Complex.exp (((t - n * t : ℝ) : ℂ) * Complex.I) = z := by
    push_cast
    rw [sub_mul, Complex.exp_sub, mul_assoc, Complex.exp_nat_mul, ht, hz, div_one]
  refine ⟨t, ht, ?_, ?_⟩
  · have e : ∀ a : Fin n, (if a = a0 then t - n * t else t) = t - (if a = a0 then n * t else 0) := by
      intro a; split_ifs <;> ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sub_self]
  · ext i j
    by_cases hij : i = j
    · subst hij
      by_cases h0 : i = a0
      · simp only [h0, diagonal_apply_eq, if_true, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]; exact ht'.symm
      · simp [h0, ht]
    · simp [hij]

theorem centre_acts : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (m : ℤ), IsParU lam → ∑ a, lam a = (m : ℝ) →
    IsHCS ε (fun a => lam a - (m : ℝ) / n) π' → ∀ z : ℂ, z ^ n = 1 → ∀ v,
    π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v := by
  intro n hn ε H _ _ π' lam m hpar hsum hHC z hz v
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  let a0 : Fin n := ⟨0, hn⟩
  obtain ⟨t, ht, hθsum, hdiag⟩ := scalar_as_torus a0 z hz
  obtain ⟨hirr, _, ⟨S0, hS0, _⟩, _⟩ := hHC
  obtain ⟨hΛsum, _, _, _, ⟨v0, _, hv0, hwt⟩, _⟩ := hS0
  obtain ⟨k, hk⟩ := lowCh_shift_int ε lam hpar ((m : ℝ) / n) a0
  set Λ := lowCh ε (fun a => lam a - (m : ℝ) / n)

  have hscal : ∑ a, Λ a * (if a = a0 then t - n * t else t) = -(n : ℝ) * t * k + t * m := by
    have e : ∀ a : Fin n, Λ a * (if a = a0 then t - n * t else t) = Λ a * t - (if a = a0 then Λ a0 * (n * t) else 0) := by
      intro a; split_ifs with h
      · subst h; ring
      · ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq', mem_univ, if_true, ← Finset.sum_mul, hΛsum, zero_mul]
    rw [hk]; field_simp; ring
  have key : π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v0 = z ^ m • v0 := by
    rw [hdiag, hwt _ hθsum, hscal]
    congr 1
    have e2 : (((-(n : ℝ) * t * k + t * m : ℝ)) : ℂ) * Complex.I
        = ((-((n : ℤ) * k) : ℤ) : ℂ) * ((t : ℂ) * Complex.I) + ((m : ℤ) : ℂ) * ((t : ℂ) * Complex.I) := by
      push_cast; ring
    rw [e2, Complex.exp_add, Complex.exp_int_mul, Complex.exp_int_mul, ht, _root_.zpow_neg, _root_.zpow_mul, zpow_natCast, hz,
      _root_.one_zpow, inv_one, one_mul]

  have hnorm : ‖z‖ = 1 := by
    have := congrArg norm hz
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) (by omega)).mp this
  have hzSU : z • (1 : Matrix (Fin n) (Fin n) ℂ) ∈ SUset ε := by
    refine ⟨?_, ?_⟩
    · show (z • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * Jm ε * (z • 1) = Jm ε
      have hc : z * star z = 1 := by
        rw [Complex.star_def, Complex.mul_conj', hnorm]; simp
      rw [conjTranspose_smul, conjTranspose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one,
        smul_smul, hc, one_smul]
    · rw [Matrix.det_smul, Fintype.card_fin, det_one, mul_one, hz]
  have hrep := hirr.2.2.1.1.2
  set f : H →L[ℂ] H := π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) - z ^ m • ContinuousLinearMap.id ℂ H
  have hmem : ∀ w, w ∈ LinearMap.ker (f : H →ₗ[ℂ] H) ↔ π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) w = z ^ m • w := by
    intro w
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, f, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, sub_eq_zero]
  have hclosed : IsClosed ((LinearMap.ker (f : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) := ContinuousLinearMap.isClosed_ker f
  have hstab : ∀ g ∈ SUset ε, ∀ w ∈ LinearMap.ker (f : H →ₗ[ℂ] H), π' g w ∈ LinearMap.ker (f : H →ₗ[ℂ] H) := by
    intro g hg w hw
    rw [hmem] at hw ⊢
    have hcomm : z • (1 : Matrix (Fin n) (Fin n) ℂ) * g = g * (z • 1) := by
      rw [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    have h1 := hrep _ hzSU g hg
    have h2 := hrep g hg _ hzSU
    rw [hcomm] at h1
    calc π' (z • 1) (π' g w) = ((π' (z • 1)).comp (π' g)) w := rfl
      _ = (π' g) (π' (z • 1) w) := by rw [← h1, h2]; rfl
      _ = z ^ m • π' g w := by rw [hw, map_smul]
  rcases hirr.2.2.2.1 (LinearMap.ker (f : H →ₗ[ℂ] H)) hclosed hstab with h | h
  · exact absurd (by rw [← Submodule.mem_bot ℂ, ← h, hmem]; exact key) hv0
  · exact (hmem v).mp (h ▸ Submodule.mem_top)

end GlobalTheory.SUCentre
