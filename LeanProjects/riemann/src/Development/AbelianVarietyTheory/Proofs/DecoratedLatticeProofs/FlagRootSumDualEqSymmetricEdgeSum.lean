import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlagLevelCharacterEqPsiDivN
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV GlobalTheory.FlagBasis
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RootSumDual

theorem dualIdx_lt {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : ℕ) (hi : i < n) : dualIdx ρ k i < n := by
  unfold dualIdx; split_ifs <;> omega

theorem dualIdx_invol {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : ℕ) (hi : i < n) :
    dualIdx ρ k (dualIdx ρ k i) = i := by
  unfold dualIdx; split_ifs <;> omega

def tau {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) : Equiv.Perm (Fin n) :=
  Function.Involutive.toPerm (fun i => ⟨dualIdx ρ k i.val, dualIdx_lt hn i.val i.2⟩)
    (fun i => Fin.ext (dualIdx_invol hn i.val i.2))

theorem tau_val {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : Fin n) : (tau hn i).val = dualIdx ρ k i.val := rfl

theorem tau_tau {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : Fin n) : tau hn (tau hn i) = i :=
  Fin.ext (dualIdx_invol hn i.val i.2)

def sgn (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : K := if i.val = ρ + k then -1 else 1

theorem sgn_tau (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i : Fin n) :
    sgn K ρ k (tau hn i) = sgn K ρ k i := by
  unfold sgn; rw [tau_val]; unfold dualIdx; split_ifs <;> first | rfl | (exfalso; omega)

theorem sgn_mul_self (K : Type) [CommRing K] (ρ k : ℕ) {n : ℕ} (i : Fin n) : sgn K ρ k i * sgn K ρ k i = 1 := by
  unfold sgn; split_ifs <;> simp

theorem flagGram_apply (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (i j : Fin n) :
    flagGram K n ρ k i j = if j = tau hn i then sgn K ρ k i else 0 := by
  unfold flagGram sgn; simp only [Fin.ext_iff, tau_val]

theorem flagGram_mul (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (X : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) : (flagGram K n ρ k * X) i j = sgn K ρ k i * X (tau hn i) j := by
  rw [mul_apply]; simp only [flagGram_apply K hn, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mul_flagGram (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) (X : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) : (X * flagGram K n ρ k) i j = X i (tau hn j) * sgn K ρ k j := by
  rw [mul_apply]
  have e : ∀ b : Fin n, (j = tau hn b) ↔ (b = tau hn j) := fun b =>
    ⟨fun h => by rw [h, tau_tau], fun h => by rw [h, tau_tau]⟩
  simp only [flagGram_apply K hn, e, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, sgn_tau]

theorem flagGram_mul_self (K : Type) [CommRing K] {ρ k n : ℕ} (hn : n = 2 * ρ + k + 1) :
    flagGram K n ρ k * flagGram K n ρ k = 1 := by
  ext i j
  rw [flagGram_mul K hn, flagGram_apply K hn, tau_tau, one_apply, sgn_tau]
  split_ifs with h h' h'
  · exact sgn_mul_self K ρ k i
  · exact absurd h.symm h'
  · exact absurd h'.symm h
  · exact mul_zero _

end GlobalTheory.RootSumDual

namespace GlobalTheory.RootSumDual

theorem inv_adj {K : Type} [CommRing K] {n ρ k : ℕ} {M : GL (Fin n) K} (hM : M ∈ unipSym K n ρ k) (i j : Fin n)
    (hij : j.val = i.val + 1) :
    ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = - (M : Matrix (Fin n) (Fin n) K) i j := by
  have h1 : M ∈ unip K n := hM.1
  have h := unip_mul_entry ((unip K n).inv_mem h1) h1 (show i < j by show i.val < j.val; omega)
    (fun l hil hlj => by
      have a : i.val < l.val := hil
      have b : l.val < j.val := hlj
      omega)
  rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_ne (by intro e; rw [e] at hij; omega)] at h
  linear_combination -h

theorem dual_entry {K : Type} [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (M M' : GL (Fin n) K)
    (h : (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k)
    (i j : Fin n) :
    (M' : Matrix (Fin n) (Fin n) K) (tau hn j) (tau hn i) =
      sgn K ρ k i * ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j * sgn K ρ k j := by
  set G := flagGram K n ρ k
  set Mi := ((M⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  have hMM : (M : Matrix (Fin n) (Fin n) K) * Mi = 1 := Units.mul_inv M
  have h2 : (M' : Matrix (Fin n) (Fin n) K)ᵀ * G = G * Mi := by
    conv_rhs => rw [← h, Matrix.mul_assoc _ (M : Matrix (Fin n) (Fin n) K), hMM, Matrix.mul_one]
  have h3 : (M' : Matrix (Fin n) (Fin n) K)ᵀ = G * Mi * G := by
    rw [← h2, Matrix.mul_assoc, flagGram_mul_self K hn, Matrix.mul_one]
  have h4 := congrFun (congrFun h3 (tau hn i)) (tau hn j)
  rw [transpose_apply] at h4
  rw [h4, mul_flagGram K hn, flagGram_mul K hn, tau_tau, tau_tau, sgn_tau, sgn_tau]

theorem sum_reindex {K : Type} [CommRing K] {n ρ k : ℕ} (hn : n = 2 * ρ + k + 1) (f : Fin n → Fin n → K) :
    ∑ i, ∑ j, f i j = ∑ i, ∑ j, f (tau hn j) (tau hn i) := by
  rw [Finset.sum_comm]
  refine (Equiv.sum_comp (tau hn) _).symm.trans (Finset.sum_congr rfl fun x _ => ?_)
  exact (Equiv.sum_comp (tau hn) (fun i => f i (tau hn x))).symm

theorem rootSum_dual_edges : ∀ (K : Type) [CommRing K] (n ρ k : ℕ), n = 2 * ρ + k + 1 → ∀ ε ε' a₁ a₂ : K, (ε = 1 ∧ ε' = 0) ∨ (ε = 0 ∧ ε' = 1) → a₁ ≠ 0 → a₂ ≠ 0 → ∃ a : Fin n → Fin n → K, (∀ i j, symEdge ρ k i j → a i j ≠ 0) ∧ ∀ M M' : GL (Fin n) K, (M' : Matrix (Fin n) (Fin n) K)ᵀ * flagGram K n ρ k * (M : Matrix (Fin n) (Fin n) K) = flagGram K n ρ k → M ∈ unipSym K n ρ k → a₁ * rootSum ρ k ε (M : Matrix (Fin n) (Fin n) K) + a₂ * rootSum ρ k ε' (M' : Matrix (Fin n) (Fin n) K) = ∑ i, ∑ j, if symEdge ρ k i j then a i j * (M : Matrix (Fin n) (Fin n) K) i j else 0 := by
  intro K _ n ρ k hn ε ε' a₁ a₂ hε ha₁ ha₂
  refine ⟨fun i _ => if i.val < ρ then a₁ else if i.val < ρ + k then ε * a₁ - ε' * a₂
    else if i.val = ρ + k then a₂ else -a₂, ?_, ?_⟩
  · intro i j _
    rcases hε with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> dsimp only <;> split_ifs <;> simp [ha₁, ha₂]
  · intro M M' h hM
    unfold rootSum
    rw [sum_reindex hn (fun i j => if (i.val + 1 < ρ ∧ j.val = i.val + 1) ∨ (i.val + 1 = ρ ∧ j.val = ρ + k)
      then (M' : Matrix (Fin n) (Fin n) K) i j
      else if ρ ≤ i.val ∧ j.val = i.val + 1 ∧ j.val < ρ + k then ε' * (M' : Matrix (Fin n) (Fin n) K) i j else 0)]
    simp only [dual_entry hn M M' h]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hi := i.2
    have hj := j.2
    have c1 : (((tau hn j).val + 1 < ρ ∧ (tau hn i).val = (tau hn j).val + 1) ∨
        ((tau hn j).val + 1 = ρ ∧ (tau hn i).val = ρ + k)) ↔ (j.val = i.val + 1 ∧ ρ + k ≤ i.val) := by
      simp only [tau_val]; unfold dualIdx; split_ifs <;> omega
    have c2 : (ρ ≤ (tau hn j).val ∧ (tau hn i).val = (tau hn j).val + 1 ∧ (tau hn i).val < ρ + k) ↔
        (ρ ≤ i.val ∧ j.val = i.val + 1 ∧ j.val < ρ + k) := by
      simp only [tau_val]; unfold dualIdx; split_ifs <;> omega
    have c3 : symEdge ρ k i j ↔ ((j.val = i.val + 1 ∧ i.val + 1 ≠ ρ ∧ i.val + 1 ≠ ρ + k) ∨
        (i.val + 1 = ρ ∧ j.val = ρ + k)) := Iff.rfl
    simp only [c1, c2, c3]
    by_cases hij : j.val = i.val + 1
    · rw [inv_adj hM i j hij]
      unfold sgn
      split_ifs <;> first | (exfalso; omega) | ring1
    · split_ifs <;> first | (exfalso; omega) | ring1

end GlobalTheory.RootSumDual

end
