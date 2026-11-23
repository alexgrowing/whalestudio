import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNatCastSmulCoeffIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfRowDeg
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.FockCoefInt

open MvPolynomial

def coeffSub (O : Subring ℂ) (σ : Type) : Subring (MvPolynomial σ ℂ) where
  carrier := {Q | ∀ mo, Q.coeff mo ∈ O}
  mul_mem' {a b} ha hb mo := by
    rw [coeff_mul]; exact O.sum_mem fun x _ => O.mul_mem (ha _) (hb _)
  one_mem' mo := by
    rw [coeff_one]; split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  add_mem' {a b} ha hb mo := by rw [coeff_add]; exact O.add_mem (ha mo) (hb mo)
  zero_mem' mo := by rw [coeff_zero]; exact O.zero_mem
  neg_mem' {a} ha mo := by rw [coeff_neg]; exact O.neg_mem (ha mo)

theorem C_mem_coeffSub {O : Subring ℂ} {σ : Type} {c : ℂ} (hc : c ∈ O) : (C c : MvPolynomial σ ℂ) ∈ coeffSub O σ := by
  intro mo
  rw [coeff_C]; split_ifs
  · exact hc
  · exact O.zero_mem

theorem C_pow_mul_aeval_mem {σ : Type} (O : Subring ℂ) (z : ℂ) (g : σ → MvPolynomial σ ℂ)
    (hg : ∀ v, C z * g v ∈ coeffSub O σ) (d : ℕ) (P : MvPolynomial σ ℂ) (hP : P.IsHomogeneous d)
    (hc : P ∈ coeffSub O σ) : C (z ^ d) * aeval g P ∈ coeffSub O σ := by
  rw [P.as_sum]
  rw [map_sum, Finset.mul_sum]
  refine Subring.sum_mem _ fun mo hmo => ?_
  have hdeg : ∑ v ∈ mo.support, mo v = d := by
    have := hP (mem_support_iff.mp hmo)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  rw [aeval_monomial, ← hdeg, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum, map_prod, mul_left_comm,
    ← Finset.prod_mul_distrib]
  simp_rw [map_pow, ← mul_pow]
  refine Subring.mul_mem _ ?_ (Subring.prod_mem _ fun v _ => Subring.pow_mem _ ?_ _)
  · rw [algebraMap_eq]; exact C_mem_coeffSub (hc mo)
  · exact hg v

theorem fockSubst_coeff_mem : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (u : GlobalTheory.ExportSeries.GLR D n) (O : Subring ℂ) (z : ℂ),
    (∀ τ x y, z * (((u τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) x y ∈ O ∧
      z * ((u τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) x y ∈ O) →
    ∀ (d : ℕ) (P : MvPolynomial (FVar D m n) ℂ), P.IsHomogeneous d → (∀ mo, P.coeff mo ∈ O) →
      ∀ mo, z ^ d * (GlobalTheory.ExportSeries.fockSubst p u P).coeff mo ∈ O := by
  intro D m n p u O z hu d P hP hc mo
  rw [GlobalTheory.ExportSeries.fockSubst, ← coeff_C_mul]
  refine C_pow_mul_aeval_mem O z _ ?_ d P hP hc mo
  · intro v
    split_ifs
    all_goals
      rw [Finset.mul_sum]
      refine Subring.sum_mem _ fun b _ => ?_
      rw [← mul_assoc, ← map_mul]
      intro mo'
      rw [coeff_C_mul, coeff_X']
      split_ifs
      · rw [mul_one]; first | exact (hu _ _ _).1 | exact (hu _ _ _).2
      · rw [mul_zero]; exact O.zero_mem

end GlobalTheory.FockCoefInt
