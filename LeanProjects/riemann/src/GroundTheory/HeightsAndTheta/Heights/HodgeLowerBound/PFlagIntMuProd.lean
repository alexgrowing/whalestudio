import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagIntMuProd
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagIntMuProdSlice
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial

namespace FlagIntMuProd

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ)

def muOne : MvPolynomial (Fin N) ℚ := ∑ i ∈ Finset.univ.filter (fun i : Fin N => ¬ (i : ℕ) < j), X i

def rhoBlockOne : Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => if (i : ℕ) < j then j - 1 - (i : ℕ) else N - 1 - (i : ℕ)

omit [DecidableEq Ψ] in
theorem muPoly_eq_sum : muPoly Ψ N j = ∑ τ, rename (sliceEmb τ) (muOne N j) := by
  unfold muPoly muOne
  simp only [map_sum, rename_X]
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_filter]
  rfl

theorem monomial_rhoBlock :
    (monomial (rhoBlock Ψ N j) (1 : ℚ) : RootPoly Ψ N) =
      ∏ τ, rename (sliceEmb τ) (monomial (rhoBlockOne N j) 1) := by
  simp only [rename_monomial]
  rw [← monomial_sum_prod Finset.univ (fun τ => Finsupp.mapDomain (sliceEmb τ) (rhoBlockOne N j))
    (fun _ => (1 : ℚ)), Finset.prod_const_one, sum_mapDomain_sliceEmb]
  congr 1

theorem flagInt_sum {ι : Type} (s : Finset ι) (P : ι → RootPoly Ψ N) :
    flagInt Ψ N (∑ i ∈ s, P i) = ∑ i ∈ s, flagInt Ψ N (P i) := by
  unfold flagInt antisym
  simp only [map_sum, Finset.smul_sum, coeff_sum]
  exact Finset.sum_comm

theorem flagInt_smul (c : ℚ) (P : RootPoly Ψ N) : flagInt Ψ N (c • P) = c * flagInt Ψ N P := by
  unfold flagInt antisym
  rw [coeff_sum, coeff_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [map_smul, coeff_smul, smul_eq_mul]
  ring

theorem degree_rhoOne {N j : ℕ} (hj : j ≤ N) :
    (rhoOne N).degree = j * (N - j) + (rhoBlockOne N j).degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum]
  simp only [rhoOne, rhoBlockOne, Finsupp.coe_equivFunOnFinite_symm]
  have h : ∀ i : Fin N, N - 1 - (i : ℕ) = (if (i : ℕ) < j then N - j else 0) +
      (if (i : ℕ) < j then j - 1 - (i : ℕ) else N - 1 - (i : ℕ)) := by
    intro i
    have := i.isLt
    split_ifs <;> omega
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
    add_zero, Finset.sum_const, smul_eq_mul, Fin.card_filter_val_lt, min_eq_right hj]

theorem flagIntOne_muOne_eq_zero {N j : ℕ} (hj : j ≤ N) {k : ℕ} (hk : k ≠ j * (N - j)) :
    flagIntOne N (muOne N j ^ k * monomial (rhoBlockOne N j) 1) = 0 := by
  have hμ : (muOne N j).IsHomogeneous 1 :=
    IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X ℚ i
  refine flagIntOne_eq_zero_of_isHomogeneous ((hμ.pow k).mul (isHomogeneous_monomial (1 : ℚ) rfl)) ?_
  rw [degree_rhoOne hj]
  omega

theorem flagInt_unit {k : ℕ} :
    flagInt Unit N (muPoly Unit N j ^ k * monomial (rhoBlock Unit N j) 1) =
      flagIntOne N (muOne N j ^ k * monomial (rhoBlockOne N j) 1) := by
  rw [muPoly_eq_sum, monomial_rhoBlock, Fintype.sum_unique, Fintype.prod_unique, ← map_pow, ← map_mul,
    ← Fintype.prod_unique (fun τ : Unit => rename (sliceEmb τ) (muOne N j ^ k * monomial (rhoBlockOne N j) 1)),
    flagInt_prod, Fintype.prod_unique]

end FlagIntMuProd

open FlagIntMuProd in

theorem FlagIntMuProd.proof : FlagIntMuProd.Statement := by
  intro Ψ _ _ N j hj
  set k0 : Ψ → ℕ := fun _ => j * (N - j) with hk0
  have hterm : ∀ k : Ψ → ℕ,
      ((Nat.multinomial Finset.univ k : ℕ) : RootPoly Ψ N) * (∏ τ, rename (sliceEmb τ) (muOne N j) ^ k τ) *
        ∏ τ, rename (sliceEmb τ) (monomial (rhoBlockOne N j) (1 : ℚ)) =
      ((Nat.multinomial Finset.univ k : ℕ) : ℚ) •
        ∏ τ, rename (sliceEmb τ) (muOne N j ^ k τ * monomial (rhoBlockOne N j) 1) := by
    intro k
    rw [mul_assoc, ← Finset.prod_mul_distrib, ← C_mul', map_natCast]
    simp only [map_mul, map_pow]
  rw [muPoly_eq_sum Ψ N j, monomial_rhoBlock Ψ N j, Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_mul,
    flagInt_sum]
  simp_rw [hterm, flagInt_smul, flagInt_prod]
  have hmem : k0 ∈ Finset.piAntidiag Finset.univ (dimN Ψ N j) := by
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    simp [hk0, dimN, mul_assoc]
  rw [Finset.sum_eq_single_of_mem k0 hmem]
  · have hmul : ((Nat.multinomial Finset.univ k0 : ℕ) : ℚ) =
        ((dimN Ψ N j).factorial : ℚ) / ((j * (N - j)).factorial : ℚ) ^ Fintype.card Ψ := by
      rw [eq_div_iff (by positivity)]
      have h := Nat.multinomial_spec (Finset.univ : Finset Ψ) k0
      simp only [hk0, Finset.prod_const, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
      rw [show dimN Ψ N j = Fintype.card Ψ * (j * (N - j)) by unfold dimN; ring, ← h]
      push_cast
      ring
    rw [hmul, flagInt_unit, hk0, Finset.prod_const, Finset.card_univ]
  · intro k _ hk
    obtain ⟨τ, hτ⟩ : ∃ τ, k τ ≠ j * (N - j) := by
      by_contra h
      push Not at h
      exact hk (funext h)
    rw [Finset.prod_eq_zero (Finset.mem_univ τ) (flagIntOne_muOne_eq_zero hj hτ), mul_zero]

end GroundTheory.Heights₂.Heights.LowerBoundFree
