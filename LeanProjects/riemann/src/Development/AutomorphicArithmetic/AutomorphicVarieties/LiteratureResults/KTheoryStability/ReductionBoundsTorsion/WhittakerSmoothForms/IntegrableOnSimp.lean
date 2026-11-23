import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.SimplexMem

noncomputable section

open Set Filter Topology MeasureTheory

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def simp' (q : ℕ) : Set (Fin q → ℝ) := {t | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1}

theorem isClosed_simp' (q : ℕ) : IsClosed (simp' q) := by
  have : simp' q = (⋂ j, {t : Fin q → ℝ | 0 ≤ t j}) ∩ {t | ∑ j, t j ≤ 1} := by
    ext t; simp [simp']
  rw [this]
  exact (isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)).inter
    (isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const)

theorem isCompact_simp' (q : ℕ) : IsCompact (simp' q) := by
  refine (isCompact_univ_pi fun _ => isCompact_Icc (a := (0:ℝ)) (b := 1)).of_isClosed_subset (isClosed_simp' q) ?_
  intro t ht j _
  exact ⟨ht.1 j, le_trans (Finset.single_le_sum (fun i _ => ht.1 i) (Finset.mem_univ j)) ht.2⟩

private theorem simplex_point_mem_of_convex_of_mem_simp' {U : Set V} (hU : Convex ℝ U) {q : ℕ} {y : Fin (q + 1) → V}
    (hy : ∀ j, y j ∈ U) {t : Fin q → ℝ} (ht : t ∈ simp' q) :
    y 0 + ∑ j, t j • (y j.succ - y 0) ∈ U := by
  have e : y 0 + ∑ j, t j • (y j.succ - y 0) =
      ∑ i : Fin (q + 1), (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i • y i := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, sub_smul,
      one_smul]
    abel
  rw [e]
  refine hU.sum_mem (fun i _ => ?_) ?_ (fun i _ => hy i)
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      linarith [ht.2]
    · simp only [Fin.cons_succ]
      exact ht.1 j
  · rw [Fin.sum_univ_succ]
    simp

theorem integrableOn_simp {U : Set V} (hU : Convex ℝ U) {q : ℕ} {ω : V → V [⋀^Fin q]→L[ℝ] ℝ}
    (hω : ContinuousOn ω U) {y : Fin (q + 1) → V} (hy : ∀ j, y j ∈ U) :
    IntegrableOn (fun t : Fin q → ℝ => ω (y 0 + ∑ j, t j • (y j.succ - y 0)) fun j => y j.succ - y 0)
      (simp' q) := by
  have hg : Continuous fun t : Fin q → ℝ => y 0 + ∑ j, t j • (y j.succ - y 0) := by fun_prop
  have hc : ContinuousOn (fun t : Fin q → ℝ => ω (y 0 + ∑ j, t j • (y j.succ - y 0))) (simp' q) :=
    hω.comp hg.continuousOn fun t ht => simplex_point_mem_of_convex_of_mem_simp' hU hy ht
  exact (hc.eval_const _).integrableOn_compact (isCompact_simp' q)

theorem intS'_congr {U : Set V} (hU : Convex ℝ U) {q : ℕ} {ω ω' : V → V [⋀^Fin q]→L[ℝ] ℝ}
    (h : ∀ x ∈ U, ω x = ω' x) {y : Fin (q + 1) → V} (hy : ∀ j, y j ∈ U) :
    intS' ω y = intS' ω' y := by
  unfold intS'
  refine setIntegral_congr_fun (isClosed_simp' q).measurableSet fun t ht => ?_
  simp only [h _ (simplex_point_mem_of_convex_of_mem_simp' hU hy ht)]

theorem intS'_sum {U : Set V} (hU : Convex ℝ U) {q : ℕ} {ι : Type} (s : Finset ι) (a : ι → ℝ)
    (ω : ι → V → V [⋀^Fin q]→L[ℝ] ℝ) (hω : ∀ i ∈ s, ContinuousOn (ω i) U) {y : Fin (q + 1) → V}
    (hy : ∀ j, y j ∈ U) :
    intS' (∑ i ∈ s, a i • ω i) y = ∑ i ∈ s, a i * intS' (ω i) y := by
  unfold intS'
  have e : ∀ t : Fin q → ℝ, ((∑ i ∈ s, a i • ω i) (y 0 + ∑ j, t j • (y j.succ - y 0)) fun j => y j.succ - y 0)
      = ∑ i ∈ s, a i * ω i (y 0 + ∑ j, t j • (y j.succ - y 0)) (fun j => y j.succ - y 0) := by
    intro t
    simp [Finset.sum_apply, ContinuousAlternatingMap.sum_apply]
  simp_rw [e]
  have hs := integral_finset_sum (μ := volume.restrict (simp' q)) s
    fun i hi => (integrableOn_simp hU (hω i hi) hy).const_mul (a i)
  unfold simp' at hs
  rw [hs]
  simp_rw [integral_const_mul]

end PositivityTheory.KB.WhittakerCocycle

end
