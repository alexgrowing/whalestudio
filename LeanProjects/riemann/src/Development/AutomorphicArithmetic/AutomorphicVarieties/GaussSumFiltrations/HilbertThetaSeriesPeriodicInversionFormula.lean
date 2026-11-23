import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.DualLatticeIndexEqDiscrPowMulDetPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesHolomorphicQExpansionOfBoundedCoeff
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertThetaSeriesCosetInversionFormula

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem thetaSeries_periodic_slash_frickeMatrix : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a b : F) (c : Fˣ) (T : Finset (κ → F)) (Φ : (κ → F) → ℂ), a ≠ 0 → b ≠ 0 → aL κ a ≤ aL κ b → IsReps (aL κ a) (aL κ b) T → (∀ x, Φ x ≠ 0 → x ∈ aL κ b) → (∀ x, ∀ l ∈ aL κ a, Φ (x + l) = Φ x) → sl0 k (toInf (wm c)) (th G Φ) = th G (wT G k t a c T Φ) := by
  classical
  intro F _ _ _ κ _ _ G hG t ht k hk a b c T Φ ha hb hab hT hsupp hper
  have hdec : ∀ x, Φ x = ∑ x₀ ∈ T, Φ x₀ * (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) := by
    intro x
    have e2 : ∀ x₀ ∈ T, Φ x₀ * (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) = Φ x * (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) := by
      intro x₀ _
      split_ifs with h
      · have := hper x₀ (x - x₀) h
        rw [show x₀ + (x - x₀) = x by abel] at this
        rw [this]
      · simp
    rw [Finset.sum_congr rfl e2, ← Finset.mul_sum]
    by_cases h0 : Φ x = 0
    · simp [h0]
    · obtain ⟨y, ⟨hyT, hy⟩, huniq⟩ := hT.2 x (hsupp x h0)
      rw [Finset.sum_eq_single y]
      · simp [hy]
      · intro x₀ hx₀ hne
        rw [if_neg]
        intro hm
        exact hne (huniq x₀ ⟨hx₀, hm⟩)
      · intro h
        exact absurd hyT h
  have hW : ∀ y, wT G k t a c T Φ y = ∑ x₀ ∈ T, Φ x₀ * wT G k t a c {x₀} (fun _ => 1) y := by
    intro y
    simp only [wT, Finset.sum_singleton, one_mul]
    split_ifs
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x₀ _ => by ring)
    · simp
  have hsumL : ∀ x₀ ∈ T, ∀ z : Hn F, Summable fun x => (if x - x₀ ∈ aL κ a then (1:ℂ) else 0) * ez (QF G x) z := by
    intro x₀ hx₀ z
    refine (_root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F κ G hG b _ 1 ?_ ?_).1 z
    · intro x hx
      have hm : x - x₀ ∈ aL κ a := by
        by_contra hm
        exact hx (if_neg hm)
      have := (aL κ b).add_mem (hab hm) (hT.1 x₀ hx₀)
      simpa using this
    · intro x
      split_ifs <;> simp
  have hsumR : ∀ (x₀ : κ → F) (z : Hn F), Summable fun y => wT G k t a c {x₀} (fun _ => (1:ℂ)) y * ez (QF G y) z := by
    intro x₀ z
    obtain ⟨-, ⟨N, hN, hN2⟩, -⟩ := _root_.GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hG
    have hc : (c : F) ≠ 0 := c.ne_zero
    have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
    refine (_root_.GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F κ G hG ((c:F) / ((N:F) * a)) _ ‖wC k t a (c:F)‖ ?_ ?_).1 z
    · intro y hy
      have hd : (a / c) • y ∈ dualL F G := by
        by_contra hd
        exact hy (by simp [wT, hd])
      have hw := (hN2 _ hd).1
      refine AddSubgroup.mem_map.2 ⟨_, hw, ?_⟩
      simp only [DistribMulAction.toAddMonoidHom_apply]
      rw [smul_smul, smul_smul]
      rw [show (c:F) / ((N:F) * a) * (N:F) * (a / c) = 1 by field_simp, one_smul]
    · intro y
      simp only [wT, Finset.sum_singleton, one_mul]
      split_ifs
      · simp [et, Complex.norm_exp]
      · simp
  have thL : ∀ z, th G Φ z = ∑ x₀ ∈ T, Φ x₀ * th G (fun x => if x - x₀ ∈ aL κ a then (1:ℂ) else 0) z := by
    intro z
    simp only [th]
    have e : ∀ x, Φ x * ez (QF G x) z = ∑ x₀ ∈ T, Φ x₀ * ((if x - x₀ ∈ aL κ a then (1:ℂ) else 0) * ez (QF G x) z) := by
      intro x
      rw [hdec x, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [tsum_congr e, Summable.tsum_finsetSum (fun x₀ hx₀ => (hsumL x₀ hx₀ z).mul_left (Φ x₀))]
    exact Finset.sum_congr rfl (fun x₀ _ => tsum_mul_left)
  have thR : ∀ z, th G (wT G k t a c T Φ) z = ∑ x₀ ∈ T, Φ x₀ * th G (wT G k t a c {x₀} (fun _ => (1:ℂ))) z := by
    intro z
    simp only [th]
    have e : ∀ y, wT G k t a c T Φ y * ez (QF G y) z = ∑ x₀ ∈ T, Φ x₀ * (wT G k t a c {x₀} (fun _ => (1:ℂ)) y * ez (QF G y) z) := by
      intro y
      rw [hW y, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [tsum_congr e, Summable.tsum_finsetSum (fun x₀ _ => (hsumR x₀ z).mul_left (Φ x₀))]
    exact Finset.sum_congr rfl (fun x₀ _ => tsum_mul_left)
  funext z
  rw [thR z]
  simp only [sl0]
  rw [thL, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x₀ _ => ?_)
  have := congrFun (_root_.GlobalTheory.T.hilbertThetaSeries_coset_inversion_formula F κ G hG t ht k hk a c x₀ ha) z
  simp only [sl0] at this
  rw [← this]
  ring

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertThetaSeries_periodic_inversion_formula : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → ∀ t : ℕ, G.det = (t : ℤ) ^ 2 → ∀ k : ℕ, Fintype.card κ = 2 * k → ∀ (a b : F) (c : Fˣ) (T : Finset (κ → F)) (Φ : (κ → F) → ℂ), a ≠ 0 → b ≠ 0 → aL κ a ≤ aL κ b → IsReps (aL κ a) (aL κ b) T → (∀ x, Φ x ≠ 0 → x ∈ aL κ b) → (∀ x, ∀ l ∈ aL κ a, Φ (x + l) = Φ x) → sl0 k (toInf (wm c)) (th G Φ) = th G (wT G k t a c T Φ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.thetaSeries_periodic_slash_frickeMatrix | exact GlobalTheory.HilbertThetaSeries.thetaSeries_periodic_slash_frickeMatrix | (intros; apply GlobalTheory.HilbertThetaSeries.thetaSeries_periodic_slash_frickeMatrix <;> assumption)
