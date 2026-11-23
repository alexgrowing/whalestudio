import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame.ThirdDiv

def uEl : SL(2, ℤ) := ⟨!![0, -1; 1, 1], by norm_num [Matrix.det_fin_two_of]⟩

noncomputable def μ : ℂ := ⟨1 / 2, Real.sqrt 3 / 2⟩

theorem μ_sq : μ ^ 2 = μ - 1 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply Complex.ext <;> simp [μ, pow_two] <;> nlinarith [h3]

theorem coe_ρ : (ρ : ℂ) = μ - 1 := by
  apply Complex.ext <;> simp [μ, UpperHalfPlane.ρ] <;> norm_num

theorem μ_ne : μ ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp [μ] at this

theorem denom_uEl : denom (uEl : GL (Fin 2) ℝ) ρ = μ := by
  simp only [denom, Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
  simp [uEl, coe_ρ]

theorem uEl_smul_ρ : uEl • ρ = ρ := by
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  simp [uEl, coe_ρ]
  rw [div_eq_iff (by simpa using μ_ne), neg_eq_iff_eq_neg]
  linear_combination μ_sq

theorem re_μ_zpow {w : ℤ} (hw : Odd w) :
    (μ ^ (-w)).re = if (3 : ℤ) ∣ w then -1 else 1 / 2 := by
  have h3 : μ ^ 3 = -1 := by linear_combination (μ + 1) * μ_sq
  have h5 : μ ^ 5 = 1 - μ := by linear_combination μ ^ 2 * h3 - μ_sq
  have h6 : μ ^ (6 : ℤ) = 1 := by
    rw [zpow_ofNat]; linear_combination (μ ^ 3 - 1) * h3
  have key : ∀ q t : ℤ, μ ^ (6 * q + t) = μ ^ t := fun q t => by
    rw [zpow_add₀ μ_ne, zpow_mul, h6, one_zpow, one_mul]
  have hre : μ.re = 1 / 2 := rfl
  obtain ⟨m, hm⟩ := hw
  have hc : -w = 6 * (-w / 6) + 1 ∨ -w = 6 * (-w / 6) + 3 ∨ -w = 6 * (-w / 6) + 5 := by omega
  rcases hc with h | h | h
  · rw [if_neg (by omega), h, key, zpow_one, hre]
  · rw [if_pos (by omega), h, key, zpow_ofNat, h3]; simp
  · rw [if_neg (by omega), h, key, zpow_ofNat, h5, Complex.sub_re, hre]; norm_num

theorem not_fixed {N : ℕ} (hN : 5 ≤ N) {γ x : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma1 N) :
    ¬ (x * uEl = γ * x ∨ x * uEl = -(γ * x)) := by
  obtain ⟨h0, h1, -⟩ := (CongruenceSubgroup.Gamma1_mem N γ).1 hγ
  have htr : ((x * uEl * x⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel_left]
    simp [uEl, Matrix.trace_fin_two]
  rintro (h | h)
  · rw [h, mul_inv_cancel_right, Matrix.trace_fin_two] at htr
    have h2 := congrArg (Int.cast : ℤ → ZMod N) htr
    push_cast at h2
    have h3 : ((1 : ℕ) : ZMod N) = 0 := by
      push_cast; linear_combination h2 - h0 - h1
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).1 h3)
    omega
  · rw [h, neg_mul, mul_inv_cancel_right, Matrix.SpecialLinearGroup.coe_neg, Matrix.trace_neg,
      Matrix.trace_fin_two] at htr
    have h2 := congrArg (Int.cast : ℤ → ZMod N) htr
    push_cast at h2
    have h3 : ((3 : ℕ) : ZMod N) = 0 := by
      push_cast; linear_combination - h2 - h0 - h1
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff _ _).1 h3)
    omega

theorem three_mul_card_dvd (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (hN : 5 ≤ N) (hΓ : Γ ≤ CongruenceSubgroup.Gamma1 N) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hdet : (evM s w F ρ).det ≠ 0) :
    3 * (Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card = r := by
  classical
  obtain ⟨π, hπ⟩ := hs.exists_perm uEl
  have hε : ∀ i, ∃ ε : ℂ, ∀ j, evM s w F ρ i j * μ ^ (-w j) = ε * evM s w F ρ (π i) j := by
    intro i
    have h0 : ∀ j, (F j ∣[w j] (s i * uEl)) ρ = evM s w F ρ i j * μ ^ (-w j) := fun j => by
      rw [slash_mul_apply, uEl_smul_ρ, denom_uEl]; rfl
    obtain ⟨γ, hγ, h | h⟩ := hπ i
    · refine ⟨1, fun j => ?_⟩
      rw [← h0, h, (hF j).2.slash_mul hγ, one_mul]; rfl
    · refine ⟨-1, fun j => ?_⟩
      rw [← h0, h, slash_neg_of_odd (hF j).1, (hF j).2.slash_mul hγ, neg_one_mul]; rfl
  choose ε hε using hε
  have hne : ∀ i, π i ≠ i := fun i hi => by
    obtain ⟨γ, hγ, h⟩ := hπ i
    rw [hi] at h
    exact not_fixed hN (hΓ hγ) h
  set A := evM s w F ρ with hA
  let P : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun i i' => if i' = π i then ε i else 0
  have hAP : A * Matrix.diagonal (fun j => μ ^ (-w j)) = P * A := by
    ext i j
    rw [Matrix.mul_diagonal, hε, Matrix.mul_apply]
    simp [P]
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  have hD : Matrix.diagonal (fun j => μ ^ (-w j)) = A⁻¹ * (P * A) := by
    rw [← hAP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have htr : ∑ j, μ ^ (-w j) = 0 := by
    rw [← Matrix.trace_diagonal, hD, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
      Matrix.mul_one]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [P, (hne i).symm]
  have hre := congrArg Complex.re htr
  rw [Complex.re_sum, Finset.sum_congr rfl fun j _ => re_μ_zpow (hF j).1, Finset.sum_ite] at hre
  simp only [Finset.sum_const, nsmul_eq_mul, Complex.zero_re] at hre
  have hc := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r)))
    (fun j => (3 : ℤ) ∣ w j)
  rw [Finset.card_univ, Fintype.card_fin] at hc
  have hc' := congrArg (Nat.cast : ℕ → ℝ) hc
  push_cast at hc'
  have : (3 : ℝ) * ((Finset.univ.filter fun j => (3 : ℤ) ∣ w j).card : ℝ) = r := by linarith
  exact_mod_cast this

end GlobalTheory.OddFrame.ThirdDiv
