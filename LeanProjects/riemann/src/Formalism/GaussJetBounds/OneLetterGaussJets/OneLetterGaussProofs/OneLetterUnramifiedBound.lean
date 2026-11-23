import Formalism.GaussJetBounds.OneLetterGaussJets.StatementG
import Formalism.GaussJetBounds.GaussJetProofs.OneGauss
import Formalism.GaussJetBounds.GaussJetProofs.WeightsAddOverOrbitFamily
import Formalism.GaussJetBounds.GaussJetProofs.OrbMul

noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

open Formalism.IncomingBounds

theorem one_letter_unramified_bound (K : Type u) [NormedField K] [IsUltrametricDist K] [CharZero K]
    (l N0 N1 : ℕ) (hl : l.Prime) (hodd : Odd l) (hpi : ‖(l : K)‖ < 1)
    (K0 : Subfield K) (hK0 : Unram l K0) (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ 2 - 1))
    (be : MvPowerSeries (ZMod 2) K) (hbe : BHyp l 2 K0 ζ be) (ep : K) (hep : ‖ep‖ = 1)
    (ι : Type v) [Fintype ι] (M : Fin N0 × Fin N1 → ι → K) (hM1 : ∀ x i, ‖M x i‖ ≤ 1)
    (g : Fin N0 × Fin N1 → MvPowerSeries (Fin N0 × Fin N1) K)
    (hg0 : ∀ x, MvPowerSeries.constantCoeff (g x) = 0)
    (hg : ∀ x, MvPowerSeries.subst g (oneLog (K := K) l x) = MvPowerSeries.X x)
    (U : MvPowerSeries (Fin N0 × Fin N1) K) (hU : Integral U)
    (sgn : K) (hsgn : sgn = 1 ∨ sgn = -1) (κ : ι →₀ ℕ) (a : ℕ) (ha : 1 ≤ a)
    (hκa : ∀ i, κ i ≤ a) :
    ‖((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ
        (MvPowerSeries.subst (fun x => ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i)
            (MvPowerSeries.subst g U) *
          mvExp ((sgn / 2) • ∑ x : Fin N0 × Fin N1, MvPowerSeries.subst
            (fun s : ZMod 2 => (if s = 0 then (1 : K) else ep) •
              ∑ i, MvPowerSeries.C (M x i) * MvPowerSeries.X i) be))‖ ≤
      ‖(l : K)‖ ^ (rho l * (κ.degree : ℝ) -
        (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1)) := by
  have hl3 : 3 ≤ l := by
    obtain ⟨k, hk⟩ := hodd
    have := hl.two_le
    omega
  obtain ⟨-, hOR2⟩ := oneLetterRadius l hl3
  obtain ⟨hBc, hBw⟩ := one_letter_exponent_weight.{u, v} K l N0 N1 hl hodd hpi K0 hK0 ζ hζ be hbe ep hep ι M
    hM1 sgn hsgn
  have hg' : ∀ x, MvPowerSeries.subst g (genLog (K := K) l (id : Fin N0 × Fin N1 → _) x) =
      MvPowerSeries.X x := by
    intro x
    rw [← (logarithm_weight_comparison K l 2 N0 N1).2.2 x]
    exact hg x
  have hsig : ∀ _ : ι, (0 : ℝ) ≤ 1 / ((l : ℝ) + 1) := fun _ => by positivity
  have hUw := unipotent_weight_bound.{u, v, 0} K l hl hpi (Fin N0 × Fin N1) id g hg0 hg' U hU ι M hM1
    (fun _ => 1 / ((l : ℝ) + 1)) hsig
  have h := lemma_R_core_log_loss.{u, v} K l hl hpi ι (fun _ => 1 / ((l : ℝ) + 1)) κ a ha hκa _ _ hBc
    (fun n _ => hBw n) (fun n _ => hUw n)
  refine le_of_le_of_eq h ?_
  congr 2
  rw [hOR2, ← Finset.sum_mul, mul_comm, Finsupp.degree_eq_sum]
  push_cast
  rfl

theorem minor_monomial_exponent_le {K : Type} [Field K] {N0 N1 C : ℕ} (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) (κ : Fin N0 × Fin N1 →₀ ℕ)
    (hκ : κ ∈ (minorProd (fun (i : Fin N0) (b : Fin N1) =>
      (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K)) p hp I).support)
    (y : Fin N0 × Fin N1) : κ y ≤ C := by
  classical
  have hrow : oldRowLow (N1 := N1) (fun i k : Fin N0 => if i = k then (1 : K) else 0) =
      fun (i : Fin N0) (b : Fin N1) =>
        (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K) := by
    funext i b
    unfold oldRowLow
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h := (monoShapeLow.{0} K N0 N1 N0 C (fun i k : Fin N0 => if i = k then (1 : K) else 0)
    p hp I κ (by rw [hrow]; exact hκ)).2 y.1
  exact le_trans (Finset.single_le_sum (f := fun b : Fin N1 => κ (y.1, b))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ y.2)) h

theorem logb_max_one_const (l C : ℕ) :
    Real.logb l ((max 1 C : ℕ) : ℝ) = Real.logb l (C : ℝ) := by
  rcases Nat.eq_zero_or_pos C with h | h
  · subst h
    simp
  · rw [max_eq_right h]

open OneGauss in
theorem one_letter_gauss_bound : OneLetterGauss7 := by
  intro l _ N0 N1 C hl3 K0 hK0 ζ hζ be hbe ep hep g hg0 hg U hU sgn hsgn p hp I n
  have hlp : l.Prime := Fact.out
  obtain ⟨K, instK, hult, hchar, φ, Y, hφ, hgauss, hgen⟩ :=
    residuallyGenericExists l (Fin N0 × Fin N0)
  have := hult
  have := hchar
  have hnl : ‖(l : K)‖ = ‖(l : ℂ_[l])‖ := by rw [← map_natCast φ, hφ]
  have hl1 : ‖(l : ℂ_[l])‖ < 1 := by
    have h := norm_intCast_padicComplex l (l : ℤ)
    rw [Int.cast_natCast, Int.cast_natCast] at h
    rw [h]
    exact Padic.norm_p_lt_one
  have hl0 : 0 < ‖(l : ℂ_[l])‖ := norm_pos_iff.2 (by exact_mod_cast hlp.ne_zero)
  have hY : ∀ y, ‖Y y‖ ≤ 1 := by
    intro y
    have h := hgauss (MvPolynomial.X y)
    rw [MvPolynomial.eval₂_X] at h
    rw [h]
    refine ciSup_le fun m => ?_
    classical
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  obtain ⟨hT1, hT2, -, -⟩ := admissibleTransfer ℂ_[l] K φ hφ l 2 N0 N1 K0 ζ be
  have hcc : MvPowerSeries.constantCoeff be = 0 := Transfer.cc_of_noLow hbe.2.2.1
  have hg0' : ∀ y, MvPowerSeries.constantCoeff (MvPowerSeries.map φ (g y)) = 0 := fun y => by
    rw [MvPowerSeries.constantCoeff_map, hg0 y, map_zero]
  have hg' : ∀ y, MvPowerSeries.subst (fun y' => MvPowerSeries.map φ (g y'))
      (oneLog (K := K) l y) = MvPowerSeries.X y := by
    intro y
    have h := congrArg (MvPowerSeries.map φ) (hg y)
    rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero hg0), map_oneLog,
      MvPowerSeries.map_X] at h
    exact h
  have hR := one_letter_unramified_bound.{0, 0} K l N0 N1 hlp (hlp.odd_of_ne_two (by omega)) (hnl ▸ hl1)
    (K0.map φ) (hT1 hK0) (φ ζ) (hζ.map_of_injective φ.injective) _ (hT2 hbe) (φ ep)
    (by rw [hφ, hep]) (Fin N0 × Fin N1) (fun x i => frA Y i x)
    (fun x i => by
      unfold frA
      split_ifs
      · exact hY _
      · simp)
    _ hg0' hg' _ (Transfer.integral_map φ hφ hU) (φ sgn) (by rcases hsgn with rfl | rfl <;> simp)
  refine le_trans (le_ciSup (bddAbove_norm_coeff _) n) ?_
  rw [← hgauss, eval₂_frameJetOne φ g hg0 U sgn ep be hcc p hp I Y]
  unfold jetPair
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg hl0.le _)
    fun κ hκ => ?_
  have hdeg := degree_plain p hp I κ hκ
  have hint : ‖MvPolynomial.coeff κ (minorProd (fun (i : Fin N0) (b : Fin N1) =>
      (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K)) p hp I)‖ ≤ 1 := by
    refine minorProd_mem_opInt _ (fun i b m => ?_) p hp I κ
    classical
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  rw [mul_assoc, norm_mul]
  refine le_trans (mul_le_of_le_one_left (norm_nonneg _) hint) ?_
  refine le_of_le_of_eq (hR κ (max 1 C) (le_max_left _ _)
    (fun y => le_trans (minor_monomial_exponent_le p hp I κ hκ y) (le_max_right _ _))) ?_
  rw [hnl, hdeg, logb_max_one_const]
  simp

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
