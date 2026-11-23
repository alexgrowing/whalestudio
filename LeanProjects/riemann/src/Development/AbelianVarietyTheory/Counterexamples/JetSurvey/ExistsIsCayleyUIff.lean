import Mathlib
import Formalism.PeriodIntegrals.UpqRep
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic

open Matrix Finset PI.UpqRep

noncomputable section

namespace GlobalTheory.UnitaryCayley

lemma trace_Jm {n : ℕ} (ε : Fin n → Bool) :
    (Jm ε).trace = 2 * ((univ.filter fun i => ε i = true).card : ℂ) - n := by
  unfold Jm
  rw [Matrix.trace_diagonal]
  have : ∀ a, (if ε a = true then (1 : ℂ) else -1) = 2 * (if ε a = true then 1 else 0) - 1 := by
    intro a; split_ifs <;> norm_num
  simp_rw [this]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

lemma exists_perm {n : ℕ} (ε δ : Fin n → Bool)
    (h : (univ.filter fun i => ε i = true).card = (univ.filter fun i => δ i = true).card) :
    ∃ e : Fin n ≃ Fin n, ∀ a, δ (e a) = ε a := by
  have h1 : Fintype.card {a // ε a = true} = Fintype.card {a // δ a = true} := by
    simp only [Fintype.card_subtype]; exact h
  have h2 : Fintype.card {a // ¬ ε a = true} = Fintype.card {a // ¬ δ a = true} := by
    simp only [Fintype.card_subtype_compl, h1]
  let e1 := Fintype.equivOfCardEq h1
  let e2 := Fintype.equivOfCardEq h2
  refine ⟨(Equiv.sumCompl fun a => ε a = true).symm.trans
    ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun a => δ a = true)), fun a => ?_⟩
  by_cases ha : ε a = true
  · have := (e1 ⟨a, ha⟩).2
    simp [Equiv.sumCompl_symm_apply_of_pos (p := fun a => ε a = true) ha, ha, this]
  · have := (e2 ⟨a, ha⟩).2
    simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun a => ε a = true) ha,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    simp only [Bool.not_eq_true] at ha this
    rw [ha, this]

theorem exists_unitary {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (h2 : A * A = 1)
    (ε : Fin n → Bool) (ht : (Jm ε).trace = A.trace) :
    ∃ P ∈ Matrix.unitaryGroup (Fin n) ℂ, Pᴴ * Jm ε * P = A := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hUu : U ∈ Matrix.unitaryGroup (Fin n) ℂ := hA.eigenvectorUnitary.2
  have hl : star U * U = 1 := Unitary.star_mul_self_of_mem hUu
  have hr : U * star U = 1 := Unitary.mul_star_self_of_mem hUu
  set D : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (hA.eigenvalues i : ℂ)) with hD
  have hs : A = U * D * star U := by
    have := hA.spectral_theorem
    simpa [Unitary.conjStarAlgAut_apply, hU, hD, Function.comp_def] using this
  have hD' : D = star U * A * U := by
    rw [hs]
    calc D = (star U * U) * D * (star U * U) := by rw [hl]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hDD : D * D = 1 := by
    rw [hD']
    calc star U * A * U * (star U * A * U) = star U * (A * (U * star U) * A) * U := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hr, Matrix.mul_one, h2, Matrix.mul_one, hl]
  have hev : ∀ i, (hA.eigenvalues i : ℂ) = 1 ∨ (hA.eigenvalues i : ℂ) = -1 := by
    intro i
    have := congrFun (congrFun hDD i) i
    rw [hD, diagonal_mul_diagonal] at this
    simp only [diagonal_apply_eq, one_apply_eq] at this
    exact mul_self_eq_one_iff.mp this
  classical
  let δ : Fin n → Bool := fun i => decide ((hA.eigenvalues i : ℂ) = 1)
  have hJ : Jm δ = D := by
    unfold Jm
    rw [hD]; congr 1; funext i
    by_cases h : (hA.eigenvalues i : ℂ) = 1
    · simp only [δ, h]; simp
    · simp only [δ, h]; simp [(hev i).resolve_left h]
  have htr : (Jm ε).trace = (Jm δ).trace := by
    rw [ht, hJ, hD', Matrix.trace_mul_comm, ← Matrix.mul_assoc, hr, Matrix.one_mul]
  rw [trace_Jm, trace_Jm] at htr
  have hc : (univ.filter fun i => ε i = true).card = (univ.filter fun i => δ i = true).card := by
    have : ((univ.filter fun i => ε i = true).card : ℂ) = (univ.filter fun i => δ i = true).card := by
      linear_combination htr / 2
    exact_mod_cast this
  obtain ⟨e, he⟩ := exists_perm ε δ hc
  have hJe : Jm ε = (Jm δ).submatrix e e := by
    unfold Jm
    rw [Matrix.submatrix_diagonal_equiv]; congr 1; funext a; simp [he]
  refine ⟨(star U).submatrix e id, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, star_star, hr]
    simp
  · rw [hJe, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      ← Matrix.star_eq_conjTranspose, star_star, hJ, ← hs]
    simp

lemma trace_Hpk (k r : ℕ) : (Hpk k r).trace = (k : ℂ) - 1 := by
  unfold Matrix.trace
  have h : ∀ i : Fin (2 * r + k + 1), Matrix.diag (Hpk k r) i =
      (fun m : ℕ => (if r ≤ m ∧ m < r + k then (1 : ℂ) else 0) - (if m = r + k then 1 else 0)) i.val := by
    intro i
    have := i.isLt
    simp only [Matrix.diag, Hpk, and_true]
    split_ifs <;> first | omega | simp
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => (if r ≤ m ∧ m < r + k then (1 : ℂ) else 0) -
    (if m = r + k then 1 else 0)), Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_boole]
  have : (range (2 * r + k + 1)).filter (fun m => r ≤ m ∧ m < r + k) = Finset.Ico r (r + k) := by
    ext m; simp only [mem_filter, mem_range, Finset.mem_Ico]; omega
  rw [this, if_pos (by simp only [mem_range]; omega)]
  simp

theorem exists_isCayleyU_iff (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) :
    (∃ P, IsCayleyU k r ε P) ↔ (univ.filter fun i => ε i = true).card = k + r := by
  constructor
  · rintro ⟨P, ⟨-, hP⟩, hu⟩
    have h1 : (Hpk k r).trace = (Jm ε).trace := by
      rw [← hP, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose,
        Unitary.mul_star_self_of_mem hu, Matrix.one_mul]
    rw [trace_Hpk, trace_Jm] at h1
    have : ((univ.filter fun i => ε i = true).card : ℂ) = ((k + r : ℕ) : ℂ) := by
      push_cast at h1 ⊢; linear_combination -h1 / 2
    exact_mod_cast this
  · intro h
    obtain ⟨h1, h2, -⟩ := Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r
    obtain ⟨P, hu, hP⟩ := exists_unitary (Hpk k r) h1 h2 ε (by
      rw [trace_Hpk, trace_Jm, h]; push_cast; ring)
    exact ⟨P, ⟨⟨⟨P, star P, Unitary.mul_star_self_of_mem hu, Unitary.star_mul_self_of_mem hu⟩, rfl⟩, hP⟩, hu⟩

theorem transport {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hP : IsCayleyU k r ε P)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (P⁻¹ * g * P ∈ UH (Hpk k r) ↔ g ∈ UJset ε) ∧
    (P⁻¹ * g * P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ ↔
      g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) := by
  obtain ⟨⟨-, hH⟩, hu⟩ := hP
  have hl : Pᴴ * P = 1 := Unitary.star_mul_self_of_mem hu
  have hr : P * Pᴴ = 1 := Unitary.mul_star_self_of_mem hu
  have hi : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv hl
  have key : ∀ A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Pᴴ * A * P = Pᴴ * B * P ↔ A = B := by
    intro A B
    refine ⟨fun h => ?_, fun h => by rw [h]⟩
    have e : ∀ C : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, P * (Pᴴ * C * P) * Pᴴ = C := by
      intro C
      calc P * (Pᴴ * C * P) * Pᴴ = (P * Pᴴ) * C * (P * Pᴴ) := by simp only [Matrix.mul_assoc]
        _ = C := by rw [hr]; simp
    rw [← e A, h, e]
  have gen : ∀ J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      (Pᴴ * g * P)ᴴ * (Pᴴ * J * P) * (Pᴴ * g * P) = Pᴴ * (gᴴ * J * g) * P := by
    intro J
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc Pᴴ * (gᴴ * P) * (Pᴴ * J * P) * (Pᴴ * g * P)
        = Pᴴ * (gᴴ * (P * Pᴴ) * J * (P * Pᴴ) * g) * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hr]; simp
  rw [hi]
  constructor
  · show (Pᴴ * g * P)ᴴ * Hpk k r * (Pᴴ * g * P) = Hpk k r ↔ gᴴ * Jm ε * g = Jm ε
    rw [← hH, gen, key]
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.star_eq_conjTranspose]
    have := gen 1
    rw [Matrix.mul_one, hl, Matrix.mul_one, Matrix.mul_one] at this
    rw [this, ← key (gᴴ * g) 1, Matrix.mul_one, hl]

end GlobalTheory.UnitaryCayley
