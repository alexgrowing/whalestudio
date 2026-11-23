import Formalism.FlagUnipotentLattices.MemLpTwoOfOneTop
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Formalism.HermitianLatticeCounting.S8 MeasureTheory Filter Topology TensorProduct Finset

set_option linter.all false

noncomputable section

namespace Formalism.HermitianLatticeCounting.P

theorem assembly_of_second_bound : AssemblyB := by
  intro T _ μ E _ _ P χ W h1 h2 h0
  have e1 : (∫ x, (inner ℂ (W x) (P (fun y => (χ y : ℂ) • W y) x) : ℂ) ∂μ) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [h0] with x hx
    simp only [hx, Pi.zero_apply, inner_zero_right]
  have e2 : (∫ x, (inner ℂ (W x) ((χ x : ℂ) • W x) : ℂ) ∂μ) = ((∫ x, χ x * ‖W x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; ext x
    rw [inner_smul_right, inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [e1, e2] at h1
  have := Complex.ofReal_eq_zero.mp h1.symm
  linarith

theorem conjugate_dual_representation : ConjDual := by
  intro E _ _ _ G _ ρ hu g v
  have h1 : ρ g * star (ρ g) = 1 := (Unitary.mem_iff.mp (hu g)).2
  have h2 : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul]; simp
  have h3 : ρ g⁻¹ = star (ρ g) := by
    calc ρ g⁻¹ = ρ g⁻¹ * (ρ g * star (ρ g)) := by rw [h1, mul_one]
      _ = star (ρ g) := by rw [← mul_assoc, h2, one_mul]
  ext y
  simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply]
  rw [h3, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem residue_formula : Residue := by
  intro E _ _ n k lam u a K s₀ s₁ hinj hK H i
  have key : (∏ s ∈ univ.erase i, (lam i - lam s)) • a i = (∏ j, (lam i - s₀ + s₁ - u j)) • K := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    set P : Polynomial ℂ := ∑ i', Polynomial.C (φ (a i')) *
      ∏ s ∈ univ.erase i', (Polynomial.X + Polynomial.C (s₀ - lam s)) with hP
    set Q : Polynomial ℂ := Polynomial.C (φ K) * ∏ j, (Polynomial.X + Polynomial.C (s₁ - u j)) with hQ
    have evP : ∀ x, P.eval x = ∑ i', φ (a i') * ∏ s ∈ univ.erase i', (x + (s₀ - lam s)) := by
      intro x
      simp only [hP, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
        Polynomial.eval_add, Polynomial.eval_X]
    have evQ : ∀ x, Q.eval x = φ K * ∏ j, (x + (s₁ - u j)) := by
      intro x
      simp only [hQ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
        Polynomial.eval_add, Polynomial.eval_X]
    have hPQ : P = Q := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hfin : (Set.range fun s => lam s - s₀).Finite := Set.finite_range _
      refine hfin.infinite_compl.mono ?_
      intro x hx
      have hx' : ∀ s, x + s₀ - lam s ≠ 0 := by
        intro s h0
        apply hx
        exact ⟨s, by linear_combination -h0⟩
      have h1 := congrArg φ (H x hx')
      simp only [map_sum, map_smul, smul_eq_mul] at h1
      have hD : (∏ s, (x + s₀ - lam s)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun s _ => hx' s)
      show P.eval x = Q.eval x
      rw [evP, evQ]
      have h2 : ∀ i', φ (a i') * ∏ s ∈ univ.erase i', (x + (s₀ - lam s)) =
          (∏ s, (x + s₀ - lam s)) * ((x - (lam i' - s₀))⁻¹ * φ (a i')) := by
        intro i'
        rw [← Finset.mul_prod_erase univ (fun s => x + s₀ - lam s) (Finset.mem_univ i')]
        have h3 : x - (lam i' - s₀) = x + s₀ - lam i' := by ring
        have h4 : ∀ s, x + (s₀ - lam s) = x + s₀ - lam s := fun s => by ring
        simp only [h3, h4]
        field_simp [hx' i']
      simp only [h2]
      rw [← Finset.mul_sum, h1]
      have h5 : ∀ j, x + (s₁ - u j) = x + s₁ - u j := fun j => by ring
      simp only [h5]
      field_simp
    have h6 := congrArg (Polynomial.eval (lam i - s₀)) hPQ
    rw [evP, evQ, Finset.sum_eq_single i] at h6
    · rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, sub_eq_zero]
      have h7 : ∀ s, lam i - s₀ + (s₀ - lam s) = lam i - lam s := fun s => by ring
      have h8 : ∀ j, lam i - s₀ + (s₁ - u j) = lam i - s₀ + s₁ - u j := fun j => by ring
      simp only [h7, h8] at h6
      rw [mul_comm, h6, mul_comm]
    · intro i' _ hi'
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hi', Finset.mem_univ i⟩) (by ring), mul_zero]
    · simp
  have hc : (∏ s ∈ univ.erase i, (lam i - lam s)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro s hs
    rw [sub_ne_zero]
    intro h
    exact (Finset.mem_erase.mp hs).1 (hinj h).symm
  constructor
  · intro h0
    rw [h0, smul_zero] at key
    have := (smul_eq_zero.mp key.symm).resolve_right hK
    obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp this
    exact ⟨j, by linear_combination -hj⟩
  · rintro ⟨j, hj⟩
    have : (∏ j, (lam i - s₀ + s₁ - u j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj]; ring)
    rw [this, zero_smul] at key
    exact (smul_eq_zero.mp key).resolve_left hc

def gdet {A : Type*} [Ring A] (t : ℕ) (F : ℕ → ℕ → ℂ → A) (x : ℂ) : A :=
  ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign σ : ℤ) : A) * (List.ofFn fun p : Fin t => F (σ p) p (x - (p : ℂ))).prod

theorem swap_lt {κ q i : ℕ} (hq : q ≤ κ) (hi : i < κ) : Equiv.swap 0 q (i + 1) < κ + 1 := by
  simp only [Equiv.swap_apply_def]; split_ifs <;> omega

def rowN {n : ℕ} (r k : ℕ) (c w : ℕ → Fin n) (p : ℕ) : Fin n :=
  if p < r then c (p + 1) else if p < r + k then w (p - r) else c (p - k + 1)

def colN {n : ℕ} (r k : ℕ) (c w : ℕ → Fin n) (p : ℕ) : Fin n :=
  if p < r then c p else if p < r + k then w (p - r) else c (p - k)

def gN {n : ℕ} (r k : ℕ) (c w : ℕ → Fin n) (p : ℕ) : Fin n :=
  if p = 0 then c r else if p ≤ r then c (p - 1) else if p ≤ r + k then w (p - r - 1) else c (p - k)

theorem cyc_val {m : ℕ} (i j : Fin (m + 1)) :
    ((Fin.cycleRange i j : Fin (m + 1)) : ℕ) =
      if (j : ℕ) < i then (j : ℕ) + 1 else if (j : ℕ) = i then 0 else (j : ℕ) := by
  rcases lt_trichotomy j i with h | h | h
  · rw [Fin.coe_cycleRange_of_lt h, if_pos (show (j : ℕ) < i from h)]
  · subst h; simp
  · rw [Fin.cycleRange_of_gt h, if_neg (by have : (i : ℕ) < j := h; omega),
      if_neg (by have : (i : ℕ) < j := h; omega)]

end Formalism.HermitianLatticeCounting.P
