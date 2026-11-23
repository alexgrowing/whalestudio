import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulMulEqOfTraceEq

open Matrix

namespace GlobalTheory

def piMatUnit {I : Type} [DecidableEq I] (m : ℕ) (τ : I) (i j : Fin m) :
    I → Matrix (Fin m) (Fin m) ℂ :=
  Pi.single τ (Matrix.single i j 1)

lemma piMatUnit_mul {I : Type} [DecidableEq I] (m : ℕ) (τ τ' : I) (i j k l : Fin m) :
    piMatUnit m τ i j * piMatUnit m τ' k l =
      if τ = τ' ∧ j = k then piMatUnit m τ i l else 0 := by
  funext ρ
  simp only [piMatUnit, Pi.mul_apply]
  by_cases h1 : τ = τ'
  · subst h1
    by_cases h2 : j = k
    · subst h2
      by_cases h3 : ρ = τ
      · subst h3; simp [Matrix.single_mul_single_same]
      · simp [Pi.single_apply, h3]
    · by_cases h3 : ρ = τ
      · subst h3; simp [Matrix.single_mul_single_of_ne, h2]
      · simp [Pi.single_apply, h3, h2]
  · by_cases h3 : ρ = τ
    · subst h3
      have : ρ ≠ τ' := h1
      simp [Pi.single_apply, this, h1]
    · simp [Pi.single_apply, h3, h1]

lemma piMatUnit_decomp {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (x : I → Matrix (Fin m) (Fin m) ℂ) :
    x = ∑ τ, ∑ i, ∑ j, x τ i j • piMatUnit m τ i j := by
  funext ρ
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, piMatUnit,
    Pi.single_apply]
  simp only [show ∀ (c : Prop) [Decidable c] (M : Matrix (Fin m) (Fin m) ℂ),
      (if c then M else 0) a b = if c then M a b else 0 from fun c _ M => by split_ifs <;> rfl]
  simp [Matrix.zero_apply, Matrix.single_apply, mul_ite, ite_and, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

lemma sum_piMatUnit_diag {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (τ : I) :
    ∑ i, piMatUnit m τ i i = Pi.single τ 1 := by
  funext ρ
  ext a b
  by_cases h : ρ = τ
  · subst h
    simp only [piMatUnit, Finset.sum_apply, Matrix.sum_apply, Pi.single_eq_same, Matrix.single_apply,
      Matrix.one_apply]
    rcases eq_or_ne a b with rfl | hab
    · simp
    · simp [hab]
  · simp [piMatUnit, Finset.sum_apply, Matrix.sum_apply, Pi.single_apply, h]

lemma exists_mul_idem_mul_eq_of_trace_eq {g : ℕ} (P P' : Matrix (Fin g) (Fin g) ℂ)
    (hP : IsIdempotentElem P) (hP' : IsIdempotentElem P') (ht : P.trace = P'.trace) :
    ∃ X Y : Matrix (Fin g) (Fin g) ℂ, Y * P' * X = P := by
  first
  | exact @_root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq
  | exact _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq
  | (apply _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq ..)

theorem conj_of_trace_central_idem_eq :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (m g : ℕ), 0 < m →
      ∀ (σ σ' : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ),
        (∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace) →
          ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ x, σ' x * h = h * σ x := by
  intro I _ _ m g hm σ σ' htr
  set z : Fin m := ⟨0, hm⟩

  have hdiag : ∀ (ρ : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (τ : I),
      (ρ (Pi.single τ 1)).trace = (m : ℂ) * (ρ (piMatUnit m τ z z)).trace := by
    intro ρ τ
    have hi : ∀ i, (ρ (piMatUnit m τ i i)).trace = (ρ (piMatUnit m τ z z)).trace := by
      intro i
      have e1 : piMatUnit m τ i i = piMatUnit m τ i z * piMatUnit m τ z i := by
        rw [piMatUnit_mul]; simp
      have e2 : piMatUnit m τ z z = piMatUnit m τ z i * piMatUnit m τ i z := by
        rw [piMatUnit_mul]; simp
      rw [e1, e2, map_mul, map_mul, Matrix.trace_mul_comm]
    rw [← sum_piMatUnit_diag, map_sum, Matrix.trace_sum, Finset.sum_congr rfl (fun i _ => hi i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hidem : ∀ (ρ : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (τ : I),
      IsIdempotentElem (ρ (piMatUnit m τ z z)) := by
    intro ρ τ
    unfold IsIdempotentElem
    rw [← map_mul, piMatUnit_mul]; simp
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have htr' : ∀ τ, (σ (piMatUnit m τ z z)).trace = (σ' (piMatUnit m τ z z)).trace := by
    intro τ
    have := htr τ
    rw [hdiag σ, hdiag σ'] at this
    exact mul_left_cancel₀ hm' this
  choose X Y hYX using fun τ => exists_mul_idem_mul_eq_of_trace_eq _ _ (hidem σ τ) (hidem σ' τ) (htr' τ)
  set h : Matrix (Fin g) (Fin g) ℂ :=
    ∑ τ, ∑ i, σ' (piMatUnit m τ i z) * X τ * σ (piMatUnit m τ z i) with hh
  set h' : Matrix (Fin g) (Fin g) ℂ :=
    ∑ τ, ∑ i, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) with hh'

  have hE : ∀ τ k l, σ' (piMatUnit m τ k l) * h = h * σ (piMatUnit m τ k l) := by
    intro τ k l
    have hL : ∀ τ' i, σ' (piMatUnit m τ k l) * (σ' (piMatUnit m τ' i z) * X τ' * σ (piMatUnit m τ' z i))
        = if τ = τ' ∧ l = i then σ' (piMatUnit m τ k z) * X τ * σ (piMatUnit m τ z l) else 0 := by
      intro τ' i
      rw [← mul_assoc, ← mul_assoc, ← map_mul, piMatUnit_mul]
      split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc; rfl
      · simp
    have hR : ∀ τ' i, σ' (piMatUnit m τ' i z) * X τ' * σ (piMatUnit m τ' z i) * σ (piMatUnit m τ k l)
        = if τ = τ' ∧ k = i then σ' (piMatUnit m τ k z) * X τ * σ (piMatUnit m τ z l) else 0 := by
      intro τ' i
      rw [mul_assoc _ (σ _), ← map_mul, piMatUnit_mul]
      by_cases hc : τ' = τ ∧ i = k
      · obtain ⟨rfl, rfl⟩ := hc; simp
      · have hc' : ¬ (τ = τ' ∧ k = i) := fun h => hc ⟨h.1.symm, h.2.symm⟩
        simp [hc, hc']
    rw [hh, Finset.mul_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_mul, hL, hR]
    simp [ite_and, Finset.sum_ite_eq]
  have hint : ∀ x, σ' x * h = h * σ x := by
    intro x
    rw [piMatUnit_decomp m x]
    simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, hE]

  have hprod : ∀ τ i τ' j, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) *
      (σ' (piMatUnit m τ' j z) * X τ' * σ (piMatUnit m τ' z j))
        = if τ = τ' ∧ i = j then σ (piMatUnit m τ i i) else 0 := by
    intro τ i τ' j
    have e : σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) *
        (σ' (piMatUnit m τ' j z) * X τ' * σ (piMatUnit m τ' z j)) =
        σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i * piMatUnit m τ' j z) * X τ' *
          σ (piMatUnit m τ' z j) := by
      rw [map_mul]; simp only [mul_assoc]
    rw [e, piMatUnit_mul]
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      rw [show σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z z) * X τ * σ (piMatUnit m τ z i) =
          σ (piMatUnit m τ i z) * (Y τ * σ' (piMatUnit m τ z z) * X τ) * σ (piMatUnit m τ z i) by
            simp only [mul_assoc], hYX τ, ← map_mul, ← map_mul]
      simp [piMatUnit_mul]
    · simp
  have hrow : ∀ τ i, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) * h =
      σ (piMatUnit m τ i i) := by
    intro τ i
    rw [hh]
    simp only [Finset.mul_sum, hprod]
    simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hinv : h' * h = 1 := by
    rw [hh', Finset.sum_mul]
    simp only [Finset.sum_mul, hrow]
    rw [← map_one σ, ← Finset.univ_sum_single (1 : I → Matrix (Fin m) (Fin m) ℂ), map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Pi.one_apply, ← sum_piMatUnit_diag, map_sum]
  exact ⟨h, (Matrix.isUnit_iff_isUnit_det h).mpr (Matrix.isUnit_det_of_left_inverse hinv), hint⟩

end GlobalTheory
