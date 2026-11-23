import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.PhGramOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.HasSubstGood

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.PhGram

open PI.FglGram

variable {p : ℕ} [Fact p.Prime]

theorem good_X {σ : Type*} (i : σ) : Good (Xv (p := p) i) := by
  unfold Good
  refine ⟨by simp [PI.FglGram.Xv], ?_⟩
  unfold PI.FglGram.IntegralMv
  intro n
  unfold PI.FglGram.IsIntP
  unfold PI.FglGram.Xv
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem hP_fst {κ : Type*} [Fintype κ] (x y : κ → ℂ_[p] × ℂ_[p]) :
    (hP x y).1 = ∑ i, (x i).1 * (y i).2 := by
  unfold hP
  rw [Prod.fst_sum]
  rfl

theorem column_of (hE : Expand) : Column := by
  intro p _ l ex ph S H k c d hcd
  have hg : ∀ j, Good (mulBy l ex (c j) (Xv j : MvPowerSeries (Fin k) ℂ_[p])) := fun j =>
    goodMul p l ex ph S H (Fin k) (c j, d j) (hcd j) _ (good_X j)
  have e : lin l ex c (fun j => (Xv j : MvPowerSeries (Fin k) ℂ_[p])) =
      pt ex (∑ j, lg l (mulBy l ex (c j) (Xv j))) := by
    unfold lin
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold mulBy
    rw [lg_pt H.data (by rw [map_mul, cc_lg H.data (cc_X _), mul_zero])]
  rw [e]
  refine sTrans (hE p l ex ph S H (Fin k) k _ hg) (sAdd ?_ ?_)
  · exact sSum _ fun j _ => normSub p l ex ph S H (Fin k) (c j, d j) (hcd j) _ (good_X j)
  · exact sSum _ fun j _ => sSum _ fun j' _ =>
      moveSub p l ex ph S H (Fin k) (c j, d j) (c j', d j') (hcd j) (hcd j') _ _ (good_X j) (good_X j')

theorem gather_of (hSF : SumFirst) : Gather := by
  intro p _ l ex ph S H hC κ _ k A hA
  have hcol : ∀ i, Simeq (phAt ph (lin l ex (fun e => (A e i).1) (fun e => (Xv e : MvPowerSeries (Fin k) ℂ_[p]))))
      (∑ j, MvPowerSeries.C ((A j i).1 * (A j i).2) * phAt ph (Xv j) +
        ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'),
          be l ex ph (mulBy l ex ((A j' i).2 * (A j i).1) (Xv j)) (Xv j')) :=
    fun i => hC k (fun j => (A j i).1) (fun j => (A j i).2) (fun j => by simpa using hA j i)
  unfold PhOn GramRhs
  refine sTrans (sSum Finset.univ fun i _ => hcol i) ?_
  rw [Finset.sum_add_distrib]
  refine sAdd (sOfEq ?_) ?_
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, ← map_sum, hP_fst]
  · have e1 : (∑ i, ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'),
          be l ex ph (mulBy l ex ((A j' i).2 * (A j i).1) (Xv j)) (Xv j') : MvPowerSeries (Fin k) ℂ_[p]) =
        ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), ∑ i,
          be l ex ph (mulBy l ex ((A j' i).2 * (A j i).1) (Xv j)) (Xv j') := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
    rw [e1]
    refine sSum _ fun j _ => sSum _ fun j' _ => ?_
    have hg : ∀ i ∈ (Finset.univ : Finset κ),
        Good (mulBy l ex ((A j' i).2 * (A j i).1) (Xv j : MvPowerSeries (Fin k) ℂ_[p])) := by
      intro i _
      rw [← mulBy_mulBy H.data _ _ (cc_X _)]
      exact goodMul p l ex ph S H (Fin k) (A j' i).swap (H.swap _ (hA j' i)) _
        (goodMul p l ex ph S H (Fin k) (A j i) (hA j i) _ (good_X j))
    have h := hSF p l ex ph S H (Fin k) κ Finset.univ (fun i => (A j' i).2 * (A j i).1) (Xv j) (Xv j')
      (good_X j) (good_X j') hg
    have e2 : (hP (A j) (A j')).1 = ∑ i, (A j' i).2 * (A j i).1 := by
      rw [hP_fst]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [e2]
    exact h

theorem phGram_of_steps (hE : Expand) (hSF : SumFirst) : PI.FglGram.PhGram := by
  have hC := column_of hE
  have hG := gather_of hSF
  unfold Column at hC
  unfold Gather at hG
  unfold PI.FglGram.PhGram
  intro p _ l ex ph S hD hsw hint hadd hph hbe hbadd κ _ k A hA
  have hH : Hyps l ex ph S := Hyps.mk hD hsw hint hadd hph hbe hbadd
  exact hG p l ex ph S hH (hC p l ex ph S hH) κ k A hA

end PI.UnitaryGroupMassFormula.PhGram
