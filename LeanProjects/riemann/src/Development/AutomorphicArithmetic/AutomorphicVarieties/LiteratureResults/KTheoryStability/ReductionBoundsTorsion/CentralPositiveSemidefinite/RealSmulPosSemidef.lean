import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CentralPositiveSemidefinite.TSpan

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.CentralizerFixed

open ComplexOrder in
theorem real_smul_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M.PosDef) {a : ℝ} (ha : 0 < a) :
    (a • M).PosDef := by
  have e : a • M = (a : ℂ) • M := by ext i j; simp [Complex.real_smul]
  rw [e]
  exact h.smul (Complex.zero_lt_real.2 ha)

open ComplexOrder in
theorem real_smul_posSemidef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : M.PosSemidef) {a : ℝ}
    (ha : 0 ≤ a) : (a • M).PosSemidef := by
  have e : a • M = (a : ℂ) • M := by ext i j; simp [Complex.real_smul]
  rw [e]
  exact h.smul (Complex.zero_le_real.2 ha)

open ComplexOrder in
theorem pos_convex (L : Type) [Field L] [NumberField L] (N : ℕ) : Convex ℝ (Pos L N) := by
  intro x hx y hy a b ha hb hab w
  have e : mat (a • x + b • y) w = a • mat x w + b • mat y w := by simp
  change (mat (a • x + b • y) w).PosDef
  rw [e]
  rcases ha.lt_or_eq with ha' | ha'
  · exact (real_smul_posDef (hx w) ha').add_posSemidef (real_smul_posSemidef (hy w).posSemidef hb)
  · have hb1 : b = 1 := by linarith
    rw [← ha', hb1, zero_smul, zero_add, one_smul]
    exact hy w

theorem simplex_meas (q : ℕ) :
    MeasurableSet {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} := by
  refine IsClosed.measurableSet ?_
  refine (IsClosed.inter ?_ ?_ : IsClosed ({t : Fin q → ℝ | ∀ j, 0 ≤ t j} ∩ {t | ∑ j, t j ≤ 1}))
  · simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  · exact isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const

theorem simplex_mem {L : Type} [Field L] [NumberField L] {N q : ℕ} (y : Fin (q + 1) → Pos L N)
    (t : Fin q → ℝ) (h0 : ∀ j, 0 ≤ t j) (h1 : ∑ j, t j ≤ 1) :
    (y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1) ∈ Pos L N := by
  let c : Fin (q + 1) → ℝ := Fin.cons (1 - ∑ j, t j) t
  have e : (y 0).1 + ∑ j, t j • ((y j.succ).1 - (y 0).1) = ∑ i, c i • (y i).1 := by
    rw [Fin.sum_univ_succ]
    simp only [c, Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
      sub_smul, one_smul]
    abel
  rw [e]
  refine (pos_convex L N).sum_mem (fun i _ => ?_) ?_ (fun i _ => (y i).2)
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp only [c, Fin.cons_zero]; linarith
    · simp only [c, Fin.cons_succ]; exact h0 j
  · rw [Fin.sum_univ_succ]
    simp only [c, Fin.cons_zero, Fin.cons_succ]
    ring

theorem tSimp : TSimp := by
  intro L _ _ N q
  refine ⟨fun y t h0 h1 => simplex_mem y t h0 h1, fun ω g hg y => ?_⟩
  unfold intP intS
  refine setIntegral_congr_fun (simplex_meas q) fun t ht => ?_
  have hp := simplex_mem y t ht.1 ht.2
  have := congrArg (fun f => f fun j => (y j.succ).1 - (y 0).1) (hg _ hp)
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply] at this
  rw [← this]
  have hs : ∀ k : Pos L N, (g • k).1 = actL g k.1 := fun k => rfl
  simp only [hs, map_add, map_sum, map_smul, map_sub]
  congr 1
  funext j
  simp [map_sub]

end PositivityTheory.KB.CentralizerFixed

end
