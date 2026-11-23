import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.SumDesc

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {I : Type 1} [DecidableEq I]

def sumPM (P : I → PM.{1} K ι) : PM.{1} K ι where
  M S := ⨁ i, (P i).M S
  res h := DirectSum.lmap fun i => (P i).res h
  res_id S h x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ _ = _
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (P i).res_id]
    | add x y hx hy => simp only [map_add, hx, hy]
  res_comp h h' x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ (DirectSum.lmap _ _) = DirectSum.lmap _ _
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (P i).res_comp]
    | add x y hx hy => simp only [map_add, hx, hy]

variable (P : I → PM.{1} K ι)

def pr (i : I) (m : ℕ) : (sumPM P).cech.X m →ₗ[K] (P i).cech.X m :=
  LinearMap.pi fun t => (DirectSum.component K I (fun j => (P j).M (ent t)) i) ∘ₗ LinearMap.proj t

def inc (i : I) (m : ℕ) : (P i).cech.X m →ₗ[K] (sumPM P).cech.X m :=
  LinearMap.pi fun t => (DirectSum.lof K I (fun j => (P j).M (ent t)) i) ∘ₗ LinearMap.proj t

theorem component_res {S T : Finset ι} (h : S ⊆ T) (i : I) (x : (sumPM P).M S) :
    DirectSum.component K I (fun j => (P j).M T) i ((sumPM P).res h x) =
      (P i).res h (DirectSum.component K I (fun j => (P j).M S) i x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of j x =>
    change DirectSum.component K I _ i (DirectSum.lmap _ _) = _
    rw [← DirectSum.lof_eq_of K, DirectSum.lmap_lof]
    by_cases e : j = i
    · subst e
      simp
    · simp [DirectSum.component.of, e]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem res_lof {S T : Finset ι} (h : S ⊆ T) (i : I) (x : (P i).M S) :
    (sumPM P).res h (DirectSum.lof K I (fun j => (P j).M S) i x) =
      DirectSum.lof K I (fun j => (P j).M T) i ((P i).res h x) := DirectSum.lmap_lof _ _ _

theorem pr_d (i : I) (m : ℕ) (z : (sumPM P).cech.X m) :
    pr P i (m + 1) ((sumPM P).cech.d m z) = (P i).cech.d m (pr P i m z) := by
  rw [Cos.d_apply, Cos.d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul]
  congr 1

theorem inc_d (i : I) (m : ℕ) (y : (P i).cech.X m) :
    inc P i (m + 1) ((P i).cech.d m y) = (sumPM P).cech.d m (inc P i m y) := by
  rw [Cos.d_apply, Cos.d_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul]
  congr 1
  funext t
  exact (res_lof P _ i _).symm

theorem cochain_ext {m : ℕ} {z : (sumPM P).cech.X m} (h : ∀ i, pr P i m z = 0) : z = 0 := by
  funext t
  refine DFinsupp.ext fun i => ?_
  exact congrFun (h i) t

theorem pr_aug (i : I) (x : (sumPM P).M ∅) :
    pr P i 0 ((sumPM P).aug x) = (P i).aug (DirectSum.component K I (fun j => (P j).M ∅) i x) := by
  funext t
  exact component_res P _ i _

theorem aug_lof (i : I) (x : (P i).M ∅) :
    (sumPM P).aug (DirectSum.lof K I (fun j => (P j).M ∅) i x) = inc P i 0 ((P i).aug x) := by
  funext t
  exact res_lof P _ i _

theorem pr_inc_self (i : I) (m : ℕ) (y : (P i).cech.X m) : pr P i m (inc P i m y) = y := by
  funext t
  exact DirectSum.component.lof_self (M := fun j => (P j).M (ent t)) K i (y t)

theorem pr_inc_ne {i j : I} (e : j ≠ i) (m : ℕ) (y : (P j).cech.X m) : pr P i m (inc P j m y) = 0 := by
  funext t
  change DirectSum.component K I (fun j => (P j).M (ent t)) i (DirectSum.lof K I (fun j => (P j).M (ent t)) j (y t)) = 0
  rw [DirectSum.component.of, dif_neg e]

open Classical in
theorem decomp [Fintype ι] {m : ℕ} (z : (sumPM P).cech.X m) :
    ∃ F : Finset I, z = ∑ i ∈ F, inc P i m (pr P i m z) := by
  refine ⟨Finset.univ.biUnion fun t => DFinsupp.support (z t), sub_eq_zero.1 (cochain_ext P fun i => ?_)⟩
  rw [map_sub, map_sum]
  by_cases hi : i ∈ Finset.univ.biUnion fun t => DFinsupp.support (z t)
  · rw [Finset.sum_eq_single_of_mem i hi (fun j _ e => pr_inc_ne P e _ _), pr_inc_self, sub_self]
  · have hz : pr P i m z = 0 := by
      funext t
      by_contra hne
      exact hi (Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, DFinsupp.mem_support_iff.2 hne⟩)
    rw [hz, Finset.sum_eq_zero (fun j hj => pr_inc_ne P (ne_of_mem_of_not_mem hj hi) _ _), sub_zero]

theorem sum_ex [Fintype ι] (h : ∀ i, (P i).Ex) : (sumPM P).Ex := by
  refine ⟨fun x => ?_, fun x hx => ?_, fun y hy => ?_, fun m y hy => ?_⟩
  · refine cochain_ext P fun i => ?_
    change pr P i 1 ((sumPM P).cech.d 0 ((sumPM P).aug x)) = 0
    rw [pr_d, pr_aug]
    exact (h i).1 _
  · rw [one_smul]
    refine DFinsupp.ext fun i => ?_
    have h0 : (P i).aug (DirectSum.component K I (fun j => (P j).M ∅) i x) = 0 := by
      rw [← pr_aug, hx, map_zero]
    have h1 := (h i).2.1 _ h0
    rw [one_smul] at h1
    exact h1
  · obtain ⟨F, hF⟩ := decomp P y
    have hc : ∀ i, (P i).cech.d 0 (pr P i 0 y) = 0 := fun i => by
      rw [← pr_d]
      exact (congrArg (pr P i 1) hy).trans (map_zero _)
    choose c hc' using fun i => (h i).2.2.1 _ (hc i)
    refine ⟨∑ i ∈ F, DirectSum.lof K I (fun j => (P j).M ∅) i (c i), ?_⟩
    rw [one_smul, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hF.symm
    rw [aug_lof, hc', one_smul]
  · obtain ⟨F, hF⟩ := decomp P y
    have hc : ∀ i, (P i).cech.d (m + 1) (pr P i (m + 1) y) = 0 := fun i => by
      rw [← pr_d]
      exact (congrArg (pr P i (m + 2)) hy).trans (map_zero _)
    choose c hc' using fun i => (h i).2.2.2 m _ (hc i)
    refine ⟨∑ i ∈ F, inc P i m (c i), ?_⟩
    rw [one_smul]
    change (sumPM P).cech.d m _ = y
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hF.symm
    rw [← inc_d]
    have h2 := hc' i
    rw [one_smul] at h2
    exact congrArg (inc P i (m + 1)) h2

theorem sum_desc {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] {I : Type 1} [DecidableEq I]
    (A : I → Sy.{1} K ι) (h : ∀ i, (A i).Desc) : (sumSy A).Desc :=
  fun n => sum_ex (fun i => (A i).term n) fun i => h i n

end GlobalTheory.CompanionTheory.KunGlue.SumDesc
