import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.ThetaIsometryFactsHold
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WtHomog

open MvPolynomial

theorem coeff_aeval_diag {K : Type} [Field K] {σ : Type} (c : σ → K) (Q : MvPolynomial σ K)
    (e : σ →₀ ℕ) :
    MvPolynomial.coeff e (aeval (fun v => C (c v) * X v) Q : MvPolynomial σ K)
      = (e.prod fun v k => c v ^ k) * MvPolynomial.coeff e Q := by
  classical
  induction Q using MvPolynomial.induction_on' generalizing e with
  | monomial u a =>
    have h : (aeval (fun v => C (c v) * X v) (monomial u a) : MvPolynomial σ K)
        = monomial u ((u.prod fun v k => c v ^ k) * a) := by
      rw [aeval_monomial]
      simp only [mul_pow, Finsupp.prod_mul, ← map_pow]
      rw [show (u.prod fun v k => (C (c v ^ k) : MvPolynomial σ K))
            = C (u.prod fun v k => c v ^ k) from (map_finsuppProd C _ _).symm]
      rw [show (u.prod fun v k => (X v : MvPolynomial σ K) ^ k) = monomial u 1 from
        (monomial_eq (s := u) (a := (1 : K))).symm ▸ by simp]
      rw [algebraMap_eq, ← mul_assoc, ← C_mul, C_mul_monomial]
      simp [mul_comm]
    rw [h, coeff_monomial, coeff_monomial]
    by_cases hue : u = e
    · subst hue; simp
    · simp [hue]
  | add p q hp hq =>
    rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

theorem deg_eq_of_mem_wtPol : ∀ {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {n : ℕ} (ν : ι → Fin n → ℕ)
    (Q : MvPolynomial (ι × Fin n × Fin n) K) (hQ : Q ∈ WtPol K ν), ∀ e ∈ Q.support, ∀ τ, ∑ α, ∑ s, e (τ, α, s) = ∑ r, ν τ r := by
  intro K _ _ ι _ n ν Q hQ e he τ
  classical
  set c : ι → K := fun σ => if σ = τ then 2 else 1 with hc
  set β : ι → Matrix (Fin n) (Fin n) K := fun σ => c σ • (1 : Matrix (Fin n) (Fin n) K) with hβ
  have hc0 : ∀ σ, c σ ≠ 0 := by
    intro σ; simp only [hc]; split_ifs <;> norm_num
  have hbor : IsBor β := by
    intro σ
    refine ⟨fun r s hsr => ?_, fun r => ?_⟩
    · simp [hβ, Matrix.one_apply, (ne_of_lt hsr).symm]
    · simpa [hβ] using hc0 σ
  have hsub : colSub β = aeval (fun v : ι × Fin n × Fin n => C (c v.1) * X v) := by
    unfold colSub
    congr 1
    funext v
    obtain ⟨σ, α, s⟩ := v
    simp only [hβ, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hw := hQ β hbor
  rw [hsub] at hw
  have hcoef := congrArg (MvPolynomial.coeff e) hw
  rw [coeff_aeval_diag, coeff_smul] at hcoef
  have hne : MvPolynomial.coeff e Q ≠ 0 := mem_support_iff.mp he
  have hL : (e.prod fun v k => c v.1 ^ k) = (2 : K) ^ (∑ α, ∑ s, e (τ, α, s)) := by
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type,
      Finset.prod_eq_single τ]
    · rw [Fintype.prod_prod_type]
      simp only [hc, if_true, Finset.prod_pow_eq_pow_sum]
    · intro σ _ hσ
      simp [hc, hσ]
    · simp
  have hR : (∏ σ, ∏ r, β σ r r ^ ν σ r) = (2 : K) ^ (∑ r, ν τ r) := by
    rw [Finset.prod_eq_single τ]
    · simp [hβ, hc, Finset.prod_pow_eq_pow_sum]
    · intro σ _ hσ
      simp [hβ, hc, hσ]
    · simp
  rw [hL, hR, smul_eq_mul] at hcoef
  have heq := mul_right_cancel₀ hne hcoef
  have h2 : ((2 : ℕ) ^ (∑ α, ∑ s, e (τ, α, s))) = (2 : ℕ) ^ (∑ r, ν τ r) := by
    exact_mod_cast heq
  exact Nat.pow_right_injective (le_refl 2) h2

end GlobalTheory.Mem.WtHomog
