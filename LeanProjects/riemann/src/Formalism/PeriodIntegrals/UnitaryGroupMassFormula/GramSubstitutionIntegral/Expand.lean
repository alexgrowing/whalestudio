import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.IntegralSubst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSubstitutionIntegral.HasSubstGood
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditiveCubes.ConstantCoeffLogEqZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupSplitting.OrthogonalSplitPolarizationVanishes

noncomputable section

open Classical

namespace PI.UnitaryGroupMassFormula.PhGram.ExpandW

open PI.FglGram PI.UnitaryGroupMassFormula.PhGram

variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]} {σ : Type}

theorem cc_l (hd : Data l ex ph) : PowerSeries.constantCoeff l = 0 := by
  exact PI.UnitaryGroupMassFormula.PhGram.cc_l hd

theorem ex_l (hd : Data l ex ph) : PowerSeries.subst l ex = PowerSeries.X :=
  (PI.FglPhSplit.Wk.compositionalInverseSymm ℂ_[p] l ex hd.1 hd.2.1).2

theorem cc_lg (hd : Data l ex ph) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (lg l a) = 0 := by
  exact PI.UnitaryGroupMassFormula.PhGram.cc_lg hd ha

theorem lg_pt (hd : Data l ex ph) {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0) :
    lg l (pt ex x) = x := by
  exact PI.UnitaryGroupMassFormula.PhGram.lg_pt hd hx

theorem pt_lg (hd : Data l ex ph) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    pt ex (lg l a) = a := by
  unfold pt lg
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero (cc_l hd))
    (PowerSeries.HasSubst.of_constantCoeff_zero ha), ex_l hd,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero ha)]

theorem pt_zero (hd : Data l ex ph) : pt ex (0 : MvPowerSeries σ ℂ_[p]) = 0 := by
  exact PowerSeries.subst_zero_of_constantCoeff_zero hd.1

theorem lg_zero (hd : Data l ex ph) : lg l (0 : MvPowerSeries σ ℂ_[p]) = 0 := by
  exact PowerSeries.subst_zero_of_constantCoeff_zero (cc_l hd)

theorem phAt_zero (hd : Data l ex ph) : phAt ph (0 : MvPowerSeries σ ℂ_[p]) = 0 := by
  exact PowerSeries.subst_zero_of_constantCoeff_zero hd.2.2

theorem add_pt (hd : Data l ex ph) {x : MvPowerSeries σ ℂ_[p]} (hx : MvPowerSeries.constantCoeff x = 0)
    (b : MvPowerSeries σ ℂ_[p]) : add l ex (pt ex x) b = pt ex (x + lg l b) := by
  unfold add
  rw [lg_pt hd hx]

theorem be_zero_left (hd : Data l ex ph) {b : MvPowerSeries σ ℂ_[p]} (hb : MvPowerSeries.constantCoeff b = 0) :
    be l ex ph 0 b = 0 := by
  unfold be add
  rw [lg_zero hd, zero_add, pt_lg hd hb, phAt_zero hd]
  ring

theorem mulBy_zero (hd : Data l ex ph) (a : MvPowerSeries σ ℂ_[p]) : mulBy l ex 0 a = 0 := by
  unfold mulBy
  rw [map_zero, zero_mul, pt_zero hd]

theorem mulBy_add (hd : Data l ex ph) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (e e' : ℂ_[p]) : mulBy l ex (e + e') a = add l ex (mulBy l ex e a) (mulBy l ex e' a) := by
  unfold mulBy add
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.C e * lg l a) = 0 := by
    rw [map_mul, cc_lg hd ha, mul_zero]
  have h2 : MvPowerSeries.constantCoeff (MvPowerSeries.C e' * lg l a) = 0 := by
    rw [map_mul, cc_lg hd ha, mul_zero]
  rw [lg_pt hd h1, lg_pt hd h2, map_add, add_mul]

theorem good_zero : Good (0 : MvPowerSeries σ ℂ_[p]) := by
  exact ⟨map_zero _, fun n => by simp [IsIntP]⟩

theorem good_mulBy_sum (hGA : GoodAdd) {S : Set (ℂ_[p] × ℂ_[p])} (H : Hyps l ex ph S) {ι : Type}
    {a : MvPowerSeries σ ℂ_[p]} (ha : Good a) (s : Finset ι) (e : ι → ℂ_[p])
    (he : ∀ i ∈ s, Good (mulBy l ex (e i) a)) : Good (mulBy l ex (∑ i ∈ s, e i) a) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, mulBy_zero H.data]
    exact good_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, mulBy_add H.data ha.1]
    exact hGA p l ex ph S H σ _ _ (he i (Finset.mem_insert_self i s))
      (ih (fun j hj => he j (Finset.mem_insert_of_mem hj)))

theorem sumFirst_of (hGA : GoodAdd) (hBS : BiaddSub) : SumFirst := by
  intro p _ l ex ph S H σ ι s e a b ha hb he
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [mulBy_zero H.data, be_zero_left H.data hb.1]
    exact sRefl 0
  | insert i s hi ih =>
    have he' : ∀ j ∈ s, Good (mulBy l ex (e j) a) := fun j hj => he j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hi, Finset.sum_insert hi, mulBy_add H.data ha.1]
    have hY := good_mulBy_sum hGA H ha s e he'
    exact sTrans (sAdd (sRefl _) (ih he'))
      (sSymm (hBS p l ex ph S H σ _ _ b (he i (Finset.mem_insert_self i s)) hY hb))

theorem cc_sum_lg (hd : Data l ex ph) {m : ℕ} {a : Fin m → MvPowerSeries σ ℂ_[p]}
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) :
    MvPowerSeries.constantCoeff (∑ j, lg l (a j)) = 0 := by
  rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => cc_lg hd (ha j)

theorem pt_sum_succ (hd : Data l ex ph) {m : ℕ} (a : Fin (m + 1) → MvPowerSeries σ ℂ_[p])
    (ha : ∀ j, MvPowerSeries.constantCoeff (a j) = 0) :
    pt ex (∑ j, lg l (a j)) =
      add l ex (pt ex (∑ j : Fin m, lg l (a (Fin.castSucc j)))) (a (Fin.last m)) := by
  rw [Fin.sum_univ_castSucc, ← add_pt hd (cc_sum_lg hd (fun j => ha (Fin.castSucc j)))]

theorem pt_sum_zero (hd : Data l ex ph) (a : Fin 0 → MvPowerSeries σ ℂ_[p]) :
    pt ex (∑ j, lg l (a j)) = 0 := by
  rw [Finset.univ_eq_empty, Finset.sum_empty, pt_zero hd]

theorem good_pt_sum (hGA : GoodAdd) {S : Set (ℂ_[p] × ℂ_[p])} (H : Hyps l ex ph S) {m : ℕ}
    (a : Fin m → MvPowerSeries σ ℂ_[p]) (ha : ∀ j, Good (a j)) : Good (pt ex (∑ j, lg l (a j))) := by
  induction m with
  | zero =>
    rw [pt_sum_zero H.data]
    exact good_zero
  | succ m ih =>
    rw [pt_sum_succ H.data a (fun j => (ha j).1)]
    exact hGA p l ex ph S H σ _ _ (ih (fun j => a (Fin.castSucc j)) (fun j => ha _)) (ha _)

theorem be_pt_sum (hGA : GoodAdd) (hBS : BiaddSub) {S : Set (ℂ_[p] × ℂ_[p])} (H : Hyps l ex ph S)
    {z : MvPowerSeries σ ℂ_[p]} (hz : Good z) {m : ℕ} (a : Fin m → MvPowerSeries σ ℂ_[p])
    (ha : ∀ j, Good (a j)) : Simeq (be l ex ph (pt ex (∑ j, lg l (a j))) z) (∑ j, be l ex ph (a j) z) := by
  induction m with
  | zero =>
    rw [pt_sum_zero H.data, be_zero_left H.data hz.1, Finset.univ_eq_empty, Finset.sum_empty]
    exact sRefl 0
  | succ m ih =>
    rw [pt_sum_succ H.data a (fun j => (ha j).1), Fin.sum_univ_castSucc]
    have hX := good_pt_sum hGA H (fun j => a (Fin.castSucc j)) (fun j => ha _)
    exact sTrans (hBS p l ex ph S H σ _ _ z hX (ha _) hz)
      (sAdd (ih (fun j => a (Fin.castSucc j)) (fun j => ha _)) (sRefl _))

def rhsBy (l ex ph : PowerSeries ℂ_[p]) {m : ℕ} (a : Fin m → MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  ∑ j', (phAt ph (a j') + ∑ j, if j < j' then be l ex ph (a j) (a j') else 0)

theorem rhsBy_succ {m : ℕ} (a : Fin (m + 1) → MvPowerSeries σ ℂ_[p]) :
    rhsBy l ex ph a = rhsBy l ex ph (fun j : Fin m => a (Fin.castSucc j)) +
      (phAt ph (a (Fin.last m)) + ∑ j : Fin m, be l ex ph (a (Fin.castSucc j)) (a (Fin.last m))) := by
  unfold rhsBy
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_castSucc]
    simp [Fin.castSucc_lt_castSucc_iff, (Fin.castSucc_lt_last k).asymm]
  · rw [Fin.sum_univ_castSucc]
    simp [Fin.castSucc_lt_last]

theorem ph_pt_sum (hGA : GoodAdd) (hBS : BiaddSub) {S : Set (ℂ_[p] × ℂ_[p])} (H : Hyps l ex ph S)
    {m : ℕ} (a : Fin m → MvPowerSeries σ ℂ_[p]) (ha : ∀ j, Good (a j)) :
    Simeq (phAt ph (pt ex (∑ j, lg l (a j)))) (rhsBy l ex ph a) := by
  induction m with
  | zero =>
    rw [pt_sum_zero H.data, phAt_zero H.data]
    unfold rhsBy
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact sRefl 0
  | succ m ih =>
    rw [pt_sum_succ H.data a (fun j => (ha j).1), rhsBy_succ]
    have e : phAt ph (add l ex (pt ex (∑ j : Fin m, lg l (a (Fin.castSucc j)))) (a (Fin.last m))) =
        phAt ph (pt ex (∑ j : Fin m, lg l (a (Fin.castSucc j)))) + (phAt ph (a (Fin.last m)) +
          be l ex ph (pt ex (∑ j : Fin m, lg l (a (Fin.castSucc j)))) (a (Fin.last m))) := by
      unfold be
      ring
    rw [e]
    exact sAdd (ih (fun j => a (Fin.castSucc j)) (fun j => ha _))
      (sAdd (sRefl _) (be_pt_sum hGA hBS H (ha _) (fun j => a (Fin.castSucc j)) (fun j => ha _)))

theorem rhsBy_eq {m : ℕ} (a : Fin m → MvPowerSeries σ ℂ_[p]) :
    rhsBy l ex ph a = ∑ j, phAt ph (a j) +
      ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'), be l ex ph (a j) (a j') := by
  unfold rhsBy
  rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun j' j => if j < j' then be l ex ph (a j) (a j') else 0)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_filter]

theorem expand_of (hGA : GoodAdd) (hBS : BiaddSub) : Expand := by
  intro p _ l ex ph S H σ m a ha
  rw [← rhsBy_eq]
  exact ph_pt_sum hGA hBS H a ha

end PI.UnitaryGroupMassFormula.PhGram.ExpandW

namespace PI.UnitaryGroupMassFormula.PhGram

theorem expand_of (hGA : GoodAdd) (hBS : BiaddSub) : Expand := ExpandW.expand_of hGA hBS

theorem sumFirst_of (hGA : GoodAdd) (hBS : BiaddSub) : SumFirst := ExpandW.sumFirst_of hGA hBS

theorem gram_bilinear_expansion : Expand := expand_of goodAdd biaddSub

theorem gram_sum_first_variable : SumFirst := sumFirst_of goodAdd biaddSub

end PI.UnitaryGroupMassFormula.PhGram
