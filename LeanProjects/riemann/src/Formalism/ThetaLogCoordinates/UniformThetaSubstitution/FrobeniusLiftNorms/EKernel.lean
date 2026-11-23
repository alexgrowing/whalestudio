import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.StatementH
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EJoint
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TopsChoicePartB

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.G7

open Formalism.DworkPowerSeriesWeights (Integral frameJet jetPairPoly minorProd mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)

namespace DeterminantJetScaling

theorem det_hom {R σ : Type} [CommRing R] {h : ℕ}
    (M : Matrix (Fin h) (Fin h) (MvPolynomial σ R)) (hM : ∀ i j, (M i j).IsHomogeneous 1) :
    M.det.IsHomogeneous h := by
  rw [Matrix.det_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun π _ => ?_
  have hp : (∏ i : Fin h, M (π i) i).IsHomogeneous h := by
    have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin h))
      (fun i => M (π i) i) (fun _ => 1) (fun i _ => hM _ _)
    simpa using this
  rw [Units.smul_def]
  exact (MvPolynomial.homogeneousSubmodule _ R h).toAddSubgroup.zsmul_mem hp _

theorem minorProd_hom {R σ : Type} [CommRing R] {N0 N1 C : ℕ}
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (hrow : ∀ i b, (row i b).IsHomogeneous 1)
    (q : Fin C → ℕ) (hq : ∀ c, q c ≤ N0) (I : ∀ c, Fin (q c) → Fin N1) :
    (minorProd row q hq I).IsHomogeneous (∑ c, q c) := by
  unfold minorProd
  refine MvPolynomial.IsHomogeneous.prod _ _ _ fun c _ => ?_
  refine det_hom _ fun i j => ?_
  rw [Matrix.of_apply]
  exact hrow _ _

theorem jetPairPoly_scale {K σ ι : Type} [Field K] (ϖ : K) (d : ℕ)
    (P : MvPolynomial ι (MvPolynomial σ K)) (hP : P.IsHomogeneous d) (Th : MvPowerSeries ι K) :
    jetPairPoly P (MvPowerSeries.subst
      (fun i => MvPowerSeries.C ϖ * (MvPowerSeries.X i : MvPowerSeries ι K)) Th) =
      MvPolynomial.C (ϖ ^ d) * jetPairPoly P Th := by
  unfold jetPairPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  have hd : κ.degree = d := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hκ) (hP.coeff_eq_zero hne)
  rw [MinorFormHomogeneity.coeff_subst_scale, hd, mul_left_comm (((mfact κ : ℕ) : K)), map_mul, mul_left_comm]

theorem frameJet_scale {K : Type} [Field K] {d N0 N1 : ℕ} [NeZero d] (ϖ : K) (colN : ZMod d → ℕ)
    (q : ∀ s, Fin (colN s) → ℕ) (hq : ∀ s c, q s c ≤ N0) (I : ∀ s c, Fin (q s c) → Fin N1)
    (Th : MvPowerSeries (ZMod d × Fin N0 × Fin N1) K) :
    frameJet colN q hq I (MvPowerSeries.subst (fun x => MvPowerSeries.C ϖ *
      (MvPowerSeries.X x : MvPowerSeries (ZMod d × Fin N0 × Fin N1) K)) Th) =
      MvPolynomial.C (ϖ ^ (∑ s, ∑ c, q s c)) * frameJet colN q hq I Th := by
  unfold frameJet
  refine jetPairPoly_scale ϖ _ _ ?_ Th
  refine MvPolynomial.IsHomogeneous.prod _ _ _ fun s _ => ?_
  refine minorProd_hom _ (fun i b => ?_) _ _ _
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun _ _ => MvPolynomial.isHomogeneous_C_mul_X _ _

theorem alG_le {ν : ℕ} (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) (s : ZMod (2 * ν)) : alG TT colN hts s ≤ ∑ c, hts s c := by
  unfold alG
  split_ifs
  · rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    refine Finset.sum_le_sum fun c _ => ?_
    split_ifs with h
    · exact h.ge
    · exact Nat.zero_le _
  · exact Nat.zero_le _

theorem deg_eq {ν : ℕ} [NeZero ν] (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ)
    (hts : ∀ s, Fin (colN s) → ℕ) :
    ∑ s, ((alG TT colN hts s : ℝ) + lsG TT colN hts s) = ((∑ s, ∑ c, hts s c : ℕ) : ℝ) := by
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Nat.cast_add]
  congr 1
  unfold lsG
  exact Nat.add_sub_cancel' (alG_le TT colN hts s)

theorem norm_unif_pow {p : ℕ} [hp : Fact p.Prime] {ϖ : ℂ_[p]} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]))
    (d : ℕ) : ‖ϖ ^ d‖ = (p : ℝ) ^ (-(rhoP p * d)) := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hn : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    have h : ‖(((p : ℚ_[p]) : ℚ_[p]) : ℂ_[p])‖ = ‖(p : ℚ_[p])‖ := PadicComplex.norm_extends' p _
    have h2 : (((p : ℚ_[p]) : ℚ_[p]) : ℂ_[p]) = (p : ℂ_[p]) := by simp
    rw [h2] at h
    rw [h, Padic.norm_p]
  rw [norm_pow, norm_unif hp.out hn hϖ, Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le,
    ← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
  unfold rhoP
  congr 1
  ring

theorem descend {p : ℕ} [hp : Fact p.Prime] {ϖ : ℂ_[p]} (hϖ : ϖ ^ (p ^ 2 - 1) = (p : ℂ_[p]))
    (d : ℕ) (g : ℝ) (x y : ℂ_[p]) (hxy : x = ϖ ^ d * y)
    (hx : ‖x‖ ≤ (p : ℝ) ^ (-(g + rhoP p * d))) : ‖y‖ ≤ (p : ℝ) ^ (-g) := by
  have hpos : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rw [hxy, norm_mul, norm_unif_pow hϖ, neg_add, add_comm, Real.rpow_add hpos] at hx
  exact le_of_mul_le_mul_left hx (Real.rpow_pos_of_pos hpos _)

end DeterminantJetScaling

open DeterminantJetScaling

end Formalism.InvariantFactorPaths.G7
