import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartZeroTrdeg
import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartZeroTrdeg

variable {F : Type} [Field F] {n : ℕ}

def homogAt (p : MvPolynomial (Fin n) F) (j : Fin n) (N : ℕ) : MvPolynomial (Fin n) F :=
  ∑ α ∈ p.support, monomial α (coeff α p) * X j ^ (N - α.sum fun _ e => e)

theorem aeval_homogAt {L : Type} [Field L] [Algebra F L] (p : MvPolynomial (Fin n) F) (j : Fin n)
    (N : ℕ) (hN : p.totalDegree ≤ N) (z : Fin n → L) (hz : z j ≠ 0) :
    aeval z (homogAt p j N) = z j ^ N * aeval (fun m => z m * (z j)⁻¹) p := by
  conv_rhs => rw [p.as_sum]
  rw [homogAt, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hk := (le_totalDegree hα).trans hN
  simp only [map_mul, aeval_monomial, map_pow, aeval_X, mul_pow, Finsupp.prod_mul]
  have hc : (α.prod fun a => HPow.hPow (z j)⁻¹) = (z j)⁻¹ ^ (α.sum fun _ e => e) := by
    simp only [Finsupp.prod, Finsupp.sum]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [hc]
  have : z j ^ N = z j ^ (N - α.sum fun _ e => e) * z j ^ (α.sum fun _ e => e) := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [this, inv_pow]
  field_simp

theorem aeval_genPt_eq_zero_iff' (P : Ideal (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = 0 ↔ f ∈ P := by
  have h : aeval (genPt P) = (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ P)
      (FractionRing (MvPolynomial (Fin n) F ⧸ P))).comp (Ideal.Quotient.mkₐ F P) :=
    MvPolynomial.algHom_ext fun i => by simp [genPt]
  rw [h]
  change algebraMap _ (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (Ideal.Quotient.mk P f) = 0 ↔ _
  rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

end ChartZeroTrdeg

open ChartZeroTrdeg in

theorem ChartZeroTrdeg.proof (hA : AffineChartTrdeg.Statement) : ChartZeroTrdeg.Statement := by
  intro F _ n d Q hQ hdim Ω _ _ y j hy hyj
  have := hQ.isPrime
  have hXj : X j ∉ Q := fun h => hyj (by simpa using hy _ h)
  set ξ := genPt Q
  have hξ : ξ j ≠ 0 := fun h => hXj ((aeval_genPt_eq_zero_iff' Q (X j)).1 (by simpa using h))
  set gξ := aeval (R := F) (fun m => ξ m * (ξ j)⁻¹)
  set gy := aeval (R := F) (fun m => y m * (y j)⁻¹)
  have hker : ∀ p, gξ p = 0 → gy p = 0 := by
    intro p hp
    have hH : homogAt p j p.totalDegree ∈ Q := by
      rw [← aeval_genPt_eq_zero_iff', aeval_homogAt p j _ le_rfl ξ hξ]
      simp [gξ] at hp
      simp [hp]
    have := hy _ hH
    rw [aeval_homogAt p j _ le_rfl y hyj] at this
    simpa [gy, hyj] using this
  have hAξ := hA F n d Q j hQ hdim hXj
  rw [Algebra.adjoin_range_eq_range_aeval] at hAξ ⊢
  let e := Ideal.quotientKerAlgEquivOfSurjective gξ.rangeRestrict_surjective
  let φ := Ideal.Quotient.liftₐ (RingHom.ker gξ.rangeRestrict) gy.rangeRestrict fun p hp => by
    apply Subtype.ext
    exact hker p (congrArg Subtype.val hp)
  have hφ : Function.Surjective φ := by
    intro b
    obtain ⟨p, hp⟩ := gy.rangeRestrict_surjective b
    exact ⟨Ideal.Quotient.mk _ p, hp⟩
  have := trdeg_le_of_surjective (φ.comp e.symm.toAlgHom) (hφ.comp e.symm.surjective)
  exact this.trans hAξ.le

end

end GroundTheory.Heights₂.Heights
