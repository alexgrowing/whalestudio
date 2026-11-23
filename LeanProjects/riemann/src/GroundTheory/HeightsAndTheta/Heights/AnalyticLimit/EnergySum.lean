import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open scoped ContDiff ComplexOrder
open ReciprocityTheory.AnForm (hessC maDens mdisc levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential mInt ChartPartition locDens integralWith)

noncomputable section

open scoped Classical in

def tvInt {D : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas D X) (Φ : Fin D → LocPot X)
    (g : X → ℝ) : ℝ :=
  if h : Nonempty (ChartPartition A) then
    ∑ j, ∫ y in (A.chart j).target,
      h.some.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) * |locDens A Φ j y|
  else 0

def EnergySum.Statement : Prop :=
  ∀ (D : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas D X) (Yo : Set X) (m : ℕ)
    (P : Fin m → LocPot X) (a : Fin D → Fin m → ℝ) (V : ℝ),
    (∀ i, IsPotential A (P i)) → (∀ i, FormNonneg A Yo (P i)) →
    (∀ σ : Fin D → Fin m,
      (∀ (Q : ChartPartition A) (j : Fin A.n), IntegrableOn (fun y =>
          Q.χ j ((A.chart j).symm y) * Yo.indicator 1 ((A.chart j).symm y) *
            locDens A (fun k => P (σ k)) j y) (A.chart j).target) ∧
      mInt A (fun k => P (σ k)) (Yo.indicator 1) ≤ V) →
    tvInt A (fun k => lincomb m (a k) P) (Yo.indicator 1) ≤ (∏ k, ∑ i, |a k i|) * V

section Proof

variable {D : ℕ}

theorem norm_mdisc_sum_le {m : ℕ} (a : Fin D → Fin m → ℝ)
    (B : Fin D → Fin m → Matrix (Fin D) (Fin D) ℂ) (hB : ∀ k i, (B k i).PosSemidef) :
    ‖mdisc (fun k => ∑ i, (a k i : ℂ) • B k i)‖ ≤
      ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * (mdisc fun k => B k (σ k)).re := by
  obtain ⟨M, hM⟩ := ReciprocityTheory.AnForm.A.exists_multilinearMap_eq_mdisc (D := D)
  rw [← hM, MultilinearMap.map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
  rw [MultilinearMap.map_smul_univ, norm_smul, hM, norm_prod]
  obtain ⟨him, hre⟩ := ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef _ fun k => hB k (σ k)
  have hz : mdisc (fun k => B k (σ k)) = ((mdisc fun k => B k (σ k)).re : ℂ) :=
    Complex.ext (by simp) (by simp [him])
  rw [hz, Complex.norm_of_nonneg hre]
  simp [Complex.norm_real]

theorem hessC_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → (Fin D → ℂ) → ℝ)
    (z : Fin D → ℂ) (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) z) :
    hessC (fun w => ∑ i ∈ s, c i * f i w) z = ∑ i ∈ s, (c i : ℂ) • hessC (f i) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := ReciprocityTheory.AnForm.M.hessC_const_mul' (D := D) 0 (fun _ => (0 : ℝ)) z
    simpa using h
  | insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    rw [ReciprocityTheory.AnForm.M.hessC_add' _ _ z (contDiffAt_const.mul (hf i (Finset.mem_insert_self _ _)))
      (ContDiffAt.sum fun i' hi' => contDiffAt_const.mul (hf i' (Finset.mem_insert_of_mem hi'))),
      ReciprocityTheory.AnForm.M.hessC_const_mul', ih fun i' hi' => hf i' (Finset.mem_insert_of_mem hi')]

variable {X : Type*} [TopologicalSpace X]

theorem abs_locDens_lincomb_le (A : FinHolAtlas D X) (Yo : Set X) {m : ℕ} (P : Fin m → LocPot X)
    (a : Fin D → Fin m → ℝ) (hpot : ∀ i, IsPotential A (P i)) (hnn : ∀ i, FormNonneg A Yo (P i))
    (j : Fin A.n) (y : Fin D → ℂ) (hy : y ∈ (A.chart j).target) (hY : (A.chart j).symm y ∈ Yo) :
    |locDens A (fun k => lincomb m (a k) P) j y| ≤
      ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * locDens A (fun k => P (σ k)) j y := by
  have hmem : ∀ i, (A.chart j).symm y ∈ (P i).U ((A.chart j).symm y) := fun i => (P i).mem_U _
  let f : Fin m → (Fin D → ℂ) → ℝ := fun i y' => (P i).φ ((A.chart j).symm y) ((A.chart j).symm y')
  have hC : ∀ i, ContDiffAt ℝ 2 (f i) y := fun i =>
    (((hpot i).1 _ j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm
      ((P i).isOpen_U _)).mem_nhds ⟨hy, hmem i⟩)).of_le (by first | simp | exact WithTop.coe_le_coe.mpr le_top)
  have hP : ∀ i, (hessC (f i) y).PosSemidef := fun i =>
    ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hC i) fun w => hnn i _ j y ⟨hy, hY, hmem i⟩ w
  have hS : ∀ k, hessC (fun y' => (lincomb m (a k) P).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      ∑ i, (a k i : ℂ) • hessC (f i) y := fun k => by
    simp_rw [lincomb_φ]
    exact hessC_finset_sum _ _ f y fun i _ => hC i
  have hc : (0 : ℝ) ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg zero_le_two Real.pi_pos.le) _)
  have hL : locDens A (fun k => lincomb m (a k) P) j y =
      (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mdisc fun k => ∑ i, (a k i : ℂ) • hessC (f i) y).re := by
    simp only [locDens, maDens, hS]
  have hR : ∀ σ : Fin D → Fin m, locDens A (fun k => P (σ k)) j y =
      (D.factorial : ℝ) * (2 / Real.pi) ^ D * (mdisc fun k => hessC (f (σ k)) y).re := fun σ => rfl
  rw [hL, abs_mul, abs_of_nonneg hc]
  calc (D.factorial : ℝ) * (2 / Real.pi) ^ D *
        |(mdisc fun k => ∑ i, (a k i : ℂ) • hessC (f i) y).re|
      ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D *
          ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * (mdisc fun k => hessC (f (σ k)) y).re :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans
          (norm_mdisc_sum_le a (fun k i => hessC (f i) y) fun _ i => hP i)) hc
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [hR]
        ring

theorem tvInt_lincomb_le (A : FinHolAtlas D X) (Yo : Set X) {m : ℕ} (P : Fin m → LocPot X)
    (a : Fin D → Fin m → ℝ) (hpot : ∀ i, IsPotential A (P i)) (hnn : ∀ i, FormNonneg A Yo (P i))
    (hint : ∀ (σ : Fin D → Fin m) (Q : ChartPartition A) (j : Fin A.n), IntegrableOn (fun y =>
      Q.χ j ((A.chart j).symm y) * Yo.indicator 1 ((A.chart j).symm y) *
        locDens A (fun k => P (σ k)) j y) (A.chart j).target) :
    tvInt A (fun k => lincomb m (a k) P) (Yo.indicator 1) ≤
      ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * mInt A (fun k => P (σ k)) (Yo.indicator 1) := by
  unfold tvInt mInt
  split_ifs with h
  · simp only [integralWith]
    calc ∑ j, ∫ y in (A.chart j).target, h.some.χ j ((A.chart j).symm y) *
            Yo.indicator 1 ((A.chart j).symm y) * |locDens A (fun k => lincomb m (a k) P) j y|
        ≤ ∑ j, ∫ y in (A.chart j).target, ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) *
            (h.some.χ j ((A.chart j).symm y) * Yo.indicator 1 ((A.chart j).symm y) *
              locDens A (fun k => P (σ k)) j y) := by
          refine Finset.sum_le_sum fun j _ => integral_mono_of_nonneg ?_
            (integrable_finsetSum _ fun σ _ => (hint σ h.some j).const_mul _) ?_
          · exact Filter.Eventually.of_forall fun y => mul_nonneg (mul_nonneg (h.some.nonneg j _)
              (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) (abs_nonneg _)
          · refine (ae_restrict_iff' (A.chart j).open_target.measurableSet).2
              (Filter.Eventually.of_forall fun y hy => ?_)
            by_cases hY : (A.chart j).symm y ∈ Yo
            · simp only [Set.indicator_of_mem hY, Pi.one_apply, mul_one]
              calc h.some.χ j ((A.chart j).symm y) * |locDens A (fun k => lincomb m (a k) P) j y|
                  ≤ h.some.χ j ((A.chart j).symm y) * ∑ σ : Fin D → Fin m,
                      (∏ k, |a k (σ k)|) * locDens A (fun k => P (σ k)) j y :=
                    mul_le_mul_of_nonneg_left
                      (abs_locDens_lincomb_le A Yo P a hpot hnn j y hy hY) (h.some.nonneg j _)
                _ = _ := by
                    rw [Finset.mul_sum]
                    exact Finset.sum_congr rfl fun σ _ => by ring
            · simp [hY]
      _ = ∑ j, ∑ σ : Fin D → Fin m, (∏ k, |a k (σ k)|) * ∫ y in (A.chart j).target,
            h.some.χ j ((A.chart j).symm y) * Yo.indicator 1 ((A.chart j).symm y) *
              locDens A (fun k => P (σ k)) j y := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [integral_finsetSum _ fun σ _ => (hint σ h.some j).const_mul _]
          exact Finset.sum_congr rfl fun σ _ => integral_const_mul _ _
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun σ _ => (Finset.mul_sum _ _ _).symm
  · simp

theorem EnergySum.proof : EnergySum.Statement := by
  intro D X _ A Yo m P a V hpot hnn hσ
  refine (tvInt_lincomb_le A Yo P a hpot hnn fun σ => (hσ σ).1).trans ?_
  rw [Fintype.prod_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun σ _ =>
    mul_le_mul_of_nonneg_left (hσ σ).2 (Finset.prod_nonneg fun k _ => abs_nonneg _)

end Proof

section Inhabitant

open ReciprocityTheory.AnForm.M (p1 fsPot projLine_isSmoothPotential projLine_isPlurisubharmonic projectiveLine_fubiniStudy_mass_one p1i0 p1i1 projectiveLine_locDens_first_chart projectiveLine_locDens_second_chart)
open ReciprocityTheory.AnForm (fsDens integrable_fsDens)

end Inhabitant

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
