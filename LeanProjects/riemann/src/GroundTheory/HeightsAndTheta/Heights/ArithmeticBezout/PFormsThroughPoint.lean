import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFormsThroughPoint
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsThroughPointIncIdeal
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartZeroTrdeg
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsThroughTwoPointsTrdeg
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTrdegBaseAlgebraic
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PComponentOfIncIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem aeval_mul_homogeneousComponent {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {n : ℕ}
    (q : MvPolynomial (Fin n) F) (e : ℕ) (t : Ω) (x : Fin n → Ω) :
    aeval (fun m => t * x m) (homogeneousComponent e q) = t ^ e * aeval x (homogeneousComponent e q) := by
  rw [homogeneousComponent_apply, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Finset.mem_filter] at hα
  simp only [aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hdeg : Finsupp.degree α = ∑ i ∈ α.support, α i := rfl
  rw [← hα.2, hdeg]
  ring

theorem FormsThroughPoint.proof (hZ : IncidenceZeroLocus.Statement) (hI : ThroughPointIncIdeal.Statement)
    (hC : ChartZeroTrdeg.Statement) (hT : ThroughTwoPointsTrdeg.Statement)
    (hB : TrdegBaseAlgebraic.Statement) : FormsThroughPoint.Statement := by
  intro F _ n k Q hQ hdim x hx hxQ
  obtain ⟨q, hqQ, hqx⟩ := hxQ

  have h1 := ComponentOfIncIdeal.one_le_ringKrullDim_quot hQ
  obtain ⟨d, hd, hdk⟩ : ∃ d : ℕ, ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = ((d + 1 : ℕ) : WithBot ℕ∞) ∧
      d + 1 ≤ k := by
    generalize ringKrullDim (MvPolynomial (Fin n) F ⧸ Q) = D at h1 hdim ⊢
    induction D using WithBot.recBotCoe with
    | bot => exact absurd h1 (by simp)
    | coe e =>
      induction e using ENat.recTopCoe with
      | top =>
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((k : ℕ∞) : WithBot ℕ∞) := hdim
        exact absurd (WithBot.coe_le_coe.mp h') (by simp)
      | coe m =>
        have h1' : 1 ≤ m := by exact_mod_cast h1
        have hm : m ≤ k := by exact_mod_cast hdim
        refine ⟨m - 1, ?_, by omega⟩
        rw [show m - 1 + 1 = m by omega]
        rfl

  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hx
  let c : Fin n → AlgebraicClosure F := Pi.single j₀ (x j₀)⁻¹
  have hj₀' : x j₀ ≠ 0 := hj₀
  have hc : ∑ j, c j * x j = 1 := by
    rw [Finset.sum_eq_single j₀ (fun b _ hb => by simp [c, hb]) (by simp)]
    simp [c, hj₀']
  by_contra hno
  push Not at hno

  have hg := hI F n k Q x c hc hno
  let K := AlgebraicClosure F
  let R := MvPolynomial (Fin k × Fin n) K
  let Ω := AlgebraicClosure (FractionRing R)
  have hinj : Function.Injective (algebraMap R Ω) := by
    rw [IsScalarTower.algebraMap_eq R (FractionRing R) Ω]
    exact (algebraMap (FractionRing R) Ω).injective.comp (IsFractionRing.injective R (FractionRing R))
  let v : Fin k × Fin n → Ω := fun ij => algebraMap R Ω (genSubst x c ij)
  have hv : ∀ g ∈ incIdeal Q k, aeval v g = 0 := by
    intro g hgI
    have hval : aeval v g = algebraMap R Ω (aeval (genSubst x c) g) := aeval_algebraMap_apply Ω (genSubst x c) g
    rw [hval, hg g hgI, map_zero]
  obtain ⟨y, hy0, hyQ, hyv⟩ := hZ F n k Q hQ.isHomog Ω v hv

  have hnp : ∀ t : Ω, y ≠ fun m => t * algebraMap K Ω (x m) := by
    intro t ht
    obtain ⟨e, he⟩ : ∃ e, aeval x (homogeneousComponent e q) ≠ 0 := by
      by_contra h
      push Not at h
      apply hqx
      rw [← sum_homogeneousComponent q, map_sum]
      exact Finset.sum_eq_zero fun e _ => h e
    have ht0 : t ≠ 0 := by
      rintro rfl
      apply hy0
      rw [ht]
      funext m
      simp
    have hzero := hyQ _ (hQ.isHomog q hqQ e)
    have hscale := aeval_mul_homogeneousComponent q e t (algebraMap K Ω ∘ x)
    simp only [Function.comp_apply] at hscale
    rw [ht, hscale, aeval_algebraMap_apply] at hzero
    exact mul_ne_zero (pow_ne_zero _ ht0) ((map_ne_zero _).mpr he) hzero

  obtain ⟨j, hj⟩ := Function.ne_iff.mp hy0
  have hk := hT K Ω n k hinj x c hc y j hj hnp hyv
  have hb := hB F K Ω inferInstance (Fin n) (fun m => y m * (y j)⁻¹)
  have hd' := hC F n d Q hQ hd Ω y j hyQ hj
  have hkd : (k : Cardinal) ≤ d := hk.trans (hb.trans hd')
  norm_cast at hkd
  omega

end GroundTheory.Heights₂.Heights
