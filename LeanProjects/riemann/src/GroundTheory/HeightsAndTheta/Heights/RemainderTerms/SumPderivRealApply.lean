import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagBasic
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsPowerSumDecompositionHomogeneousComponent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

namespace TwoCasesDerivatives

open MvPolynomial Finset

noncomputable section

variable (f j k : ℕ)

def sumPderivReal {ι : Type*} (τ : Fin f) (s : Finset ι) (g : ι → Fin (j + k)) :
    Derivation ℝ (IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :=
  ∑ l ∈ s, pderiv (τ, g l)

theorem sumPderivReal_apply {ι : Type*} (τ : Fin f) (s : Finset ι) (g : ι → Fin (j + k))
    (P : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    sumPderivReal f j k τ s g P = ∑ l ∈ s, pderiv (τ, g l) P := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sumPderivReal]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, ← ih]
    simp [sumPderivReal, Finset.sum_insert hb]

theorem sumPderivReal_X {ι : Type*} (τ : Fin f) (s : Finset ι) (g : ι → Fin (j + k))
    (σ : Fin f) (i : Fin (j + k)) :
    sumPderivReal f j k τ s g (X (σ, i)) =
      ∑ l ∈ s, if σ = τ ∧ i = g l then (1 : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) else 0 := by
  classical
  rw [sumPderivReal_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [pderiv_X, Pi.single_apply]
  simp only [Prod.mk.injEq]

theorem deriv_restPoly (D : Derivation ℝ (IndefiniteRowSideFullHecke.RestTerms.Roots f j k) (IndefiniteRowSideFullHecke.RestTerms.Roots f j k))
    (bot : Bool) (α β : Fin f → ℝ)
    (ht : ∀ σ (a : Fin j), D (X (σ, Fin.castAdd k a)) = C (α σ))
    (hb : ∀ σ (b : Fin k), D (X (σ, Fin.natAdd j b)) = C (β σ)) :
    D (IndefiniteRowSideFullHecke.RestTerms.restPoly f j k bot) =
      C (((IndefiniteRowSideFullHecke.RestTerms.nDim f j k : ℝ) + 1) *
          (if bot then (k : ℝ) * ∑ σ, β σ else -((j : ℝ) * ∑ σ, α σ))) *
        IndefiniteRowSideFullHecke.RestTerms.degPoly f j k bot := by
  have hfib : D (IndefiniteRowSideFullHecke.RestTerms.fibClass f j k bot) = 0 := by
    unfold IndefiniteRowSideFullHecke.RestTerms.fibClass
    refine Flag.derivation_prod_eq_zero D _ _ (fun σ _ => ?_)
    cases bot <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      rw [Derivation.leibniz, ← vandermondeOf_eq_vandermonde, ← vandermondeOf_eq_vandermonde,
        Flag.derivation_vandermondeOf_eq_zero D _ (fun i i' => by simp [ht, hb]),
        Flag.derivation_vandermondeOf_eq_zero D _ (fun i i' => by simp [ht, hb]),
        smul_zero, smul_zero, add_zero]
  have hmu : D (IndefiniteRowSideFullHecke.RestTerms.muClass f j k bot) =
      C (if bot then (k : ℝ) * ∑ σ, β σ else -((j : ℝ) * ∑ σ, α σ)) := by
    cases bot <;>
      simp [IndefiniteRowSideFullHecke.RestTerms.muClass, IndefiniteRowSideFullHecke.RestTerms.smallPsum, map_sum, ht, hb, Finset.mul_sum]
  rw [IndefiniteRowSideFullHecke.RestTerms.restPoly, Derivation.leibniz, hfib, smul_zero, zero_add,
    Derivation.leibniz_pow, hmu, IndefiniteRowSideFullHecke.RestTerms.degPoly]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  simp only [map_mul, map_natCast, map_add, map_one]
  push_cast
  ring

end

end TwoCasesDerivatives

open MvPolynomial Finset TwoCasesDerivatives

theorem TwoCases.intersectionNumber_baseChange : IndefiniteRowSideFullHecke.RestTerms.TwoCases.Statement := by
  classical
  intro f j k I τ
  have hI : ∀ (c : ℝ) (P : IndefiniteRowSideFullHecke.RestTerms.Roots f j k), I (C c * P) = c * I P := by
    intro c P
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]
  have hsh : ∀ F, IndefiniteRowSideFullHecke.RestTerms.shiftAt f j k I τ F =
      I (sumPderivReal f j k τ univ (Fin.castAdd k) F) := by
    intro F
    rw [sumPderivReal_apply]
    rfl
  have hto : ∀ F, IndefiniteRowSideFullHecke.RestTerms.totalAt f j k I τ F = I (sumPderivReal f j k τ univ id F) := by
    intro F
    rw [sumPderivReal_apply]
    rfl
  have shT : ∀ σ (a : Fin j), sumPderivReal f j k τ univ (Fin.castAdd k) (X (σ, Fin.castAdd k a)) =
      C (if σ = τ then 1 else 0) := by
    intro σ a
    rw [sumPderivReal_X]
    by_cases h : σ = τ <;> simp [h, Fin.castAdd_inj]
  have shB : ∀ σ (b : Fin k), sumPderivReal f j k τ univ (Fin.castAdd k) (X (σ, Fin.natAdd j b)) =
      C 0 := by
    intro σ b
    rw [sumPderivReal_X]
    refine (Finset.sum_eq_zero fun a _ => ?_).trans C_0.symm
    rw [if_neg]
    rintro ⟨-, h⟩
    have := congrArg Fin.val h
    simp at this
    omega
  have toX : ∀ σ i, sumPderivReal f j k τ univ id (X (σ, i)) = C (if σ = τ then 1 else 0) := by
    intro σ i
    rw [sumPderivReal_X]
    by_cases h : σ = τ <;> simp [h]
  have hs : ∑ σ : Fin f, (if σ = τ then (1 : ℝ) else 0) = 1 := by simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [hsh, deriv_restPoly f j k _ true (fun σ => if σ = τ then 1 else 0) (fun _ => 0) shT shB,
      hI]
    simp
  · rw [hto, deriv_restPoly f j k _ true (fun σ => if σ = τ then 1 else 0)
      (fun σ => if σ = τ then 1 else 0) (fun σ a => toX σ _) (fun σ b => toX σ _), hI, if_pos rfl,
      hs]
    ring
  · rw [hsh, deriv_restPoly f j k _ false (fun σ => if σ = τ then 1 else 0) (fun _ => 0) shT shB,
      hI, if_neg Bool.false_ne_true, hs]
    ring
  · rw [hto, deriv_restPoly f j k _ false (fun σ => if σ = τ then 1 else 0)
      (fun σ => if σ = τ then 1 else 0) (fun σ a => toX σ _) (fun σ b => toX σ _), hI,
      if_neg Bool.false_ne_true, hs]
    ring

end GroundTheory.Heights₂.Heights.RestTerms
