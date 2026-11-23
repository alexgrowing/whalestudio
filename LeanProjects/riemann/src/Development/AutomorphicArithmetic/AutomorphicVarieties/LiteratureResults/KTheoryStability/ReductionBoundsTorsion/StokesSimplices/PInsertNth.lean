import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.StokesSimplices.SumInsertNth

noncomputable section

open MeasureTheory

namespace PositivityTheory.KB.StokesSlices

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def I {q : ℕ} (ω : V → V [⋀^Fin q]→L[ℝ] ℝ) (y : Fin (q + 1) → V) : ℝ :=
  ∫ t in Δ q, ω (y 0 + ∑ j, t j • (y j.succ - y 0)) fun j => y j.succ - y 0

lemma isCompact_Δ' (m : ℕ) : IsCompact (Δ m) := by
  have hsub : Δ m ⊆ Set.pi Set.univ (fun _ : Fin m => Set.Icc (0 : ℝ) 1) := by
    intro t ht i _
    refine ⟨ht.1 i, ?_⟩
    calc t i ≤ ∑ j, t j := Finset.single_le_sum (fun j _ => ht.1 j) (Finset.mem_univ i)
      _ ≤ 1 := ht.2
  have hcl : IsClosed (Δ m) := by
    have h1 : IsClosed {t : Fin m → ℝ | ∀ j, 0 ≤ t j} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
    have h2 : IsClosed {t : Fin m → ℝ | ∑ j, t j ≤ 1} :=
      isClosed_le (continuous_finset_sum _ fun j _ => continuous_apply j) continuous_const
    exact h1.inter h2
  exact (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hcl hsub

lemma P_cons {q : ℕ} (y : Fin (q + 2) → V) (s : Fin q → ℝ) :
    y 0 + ∑ j, (Fin.cons (1 - ∑ k, s k) s : Fin (q + 1) → ℝ) j • (y j.succ - y 0) =
      y 1 + ∑ j, s j • (y j.succ.succ - y 1) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.succ_zero_eq_one]
  have key : ∀ j : Fin q, s j • (y j.succ.succ - y 0) = s j • (y j.succ.succ - y 1) + s j • (y 1 - y 0) := by
    intro j
    rw [← smul_add]
    congr 1
    abel
  rw [Finset.sum_congr rfl (fun j _ => key j), Finset.sum_add_distrib, ← Finset.sum_smul, sub_smul, one_smul]
  abel

lemma P_insertNth {q : ℕ} (y : Fin (q + 2) → V) (i : Fin (q + 1)) (x : ℝ) (s : Fin q → ℝ) :
    y 0 + ∑ j, (i.insertNth x s : Fin (q + 1) → ℝ) j • (y j.succ - y 0) =
      y 0 + x • (y i.succ - y 0) + ∑ j, s j • (y (i.succAbove j).succ - y 0) := by
  rw [Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  rw [add_assoc]

lemma P_update {q : ℕ} (y : Fin (q + 2) → V) (t : Fin (q + 1) → ℝ) (i : Fin (q + 1)) (x : ℝ) :
    y 0 + ∑ j, (Function.update t i x) j • (y j.succ - y 0) =
      (y 0 + ∑ j, t j • (y j.succ - y 0)) + (x - t i) • (y i.succ - y 0) := by
  rw [Fin.sum_univ_succAbove _ i, Fin.sum_univ_succAbove (fun j => t j • (y j.succ - y 0)) i]
  have hne : ∀ j : Fin q, Function.update t i x (i.succAbove j) = t (i.succAbove j) := fun j =>
    Function.update_of_ne (Fin.succAbove_ne i j) _ _
  simp only [hne, Function.update_self, sub_smul]
  abel

theorem asm (hA : StokesSimplexSubdivision) (hH : SubHyp) (hS : SubSlice) (U : Set V) (hU : IsOpen U)
    (hUc : Convex ℝ U) (q : ℕ) (ω : V → V [⋀^Fin q]→L[ℝ] ℝ) (hω : ContDiffOn ℝ 1 ω U)
    (y : Fin (q + 2) → V) (hy : ∀ j, y j ∈ U) :
    ∑ k : Fin (q + 2), (-1 : ℝ) ^ (k : ℕ) * I ω (fun j => y (k.succAbove j)) =
      I (extDeriv ω) y := by
  have hmem : ∀ (m : ℕ) (z : Fin (m + 1) → V), (∀ j, z j ∈ U) →
      ∀ t ∈ Δ m, z 0 + ∑ j, t j • (z j.succ - z 0) ∈ U := by
    intro m z hz t ht
    have hw0 : ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))),
        0 ≤ (Fin.cons (1 - ∑ k, t k) t : Fin (m + 1) → ℝ) j := by
      intro j _
      refine Fin.cases ?_ (fun k => ?_) j
      · simp only [Fin.cons_zero]
        linarith [ht.2]
      · simp only [Fin.cons_succ]
        exact ht.1 k
    have hw1 : ∑ j, (Fin.cons (1 - ∑ k, t k) t : Fin (m + 1) → ℝ) j = 1 := by
      rw [Fin.sum_univ_succ]
      simp
    have hc := hUc.sum_mem hw0 hw1 (fun j _ => hz j)
    convert hc using 1
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
      sub_smul, one_smul]
    abel
  have hφ : ∀ r : Fin q → V, ContDiffOn ℝ 1 (fun z => ω z r) U := fun r =>
    (ContinuousAlternatingMap.apply ℝ V ℝ r).contDiff.comp_contDiffOn hω
  have hφd : ∀ r : Fin q → V, ∀ z ∈ U,
      HasFDerivAt (fun z => ω z r) (fderiv ℝ (fun z => ω z r) z) z := fun r z hz =>
    (((hφ r).differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz)).hasFDerivAt
  have hφc : ∀ r : Fin q → V, ContinuousOn (fun z => ω z r) U := fun r => (hφ r).continuousOn
  have hφdc : ∀ r : Fin q → V, ContinuousOn (fderiv ℝ (fun z => ω z r)) U := fun r =>
    (hφ r).continuousOn_fderiv_of_isOpen hU le_rfl
  set P : (Fin (q + 1) → ℝ) → V := fun t => y 0 + ∑ j, t j • (y j.succ - y 0) with hP
  have hPc : Continuous P :=
    continuous_const.add (continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const)
  have hW : IsOpen (P ⁻¹' U) := hU.preimage hPc
  have hΔW : Δ (q + 1) ⊆ P ⁻¹' U := fun t ht => hmem (q + 1) y hy t ht
  have hmeas : ∀ m, MeasurableSet (Δ m) := fun m => (isCompact_Δ' m).isClosed.measurableSet
  have hslice : ∀ i : Fin (q + 1),
      ∫ t in Δ (q + 1), fderiv ℝ (fun z => ω z (i.removeNth fun j => y j.succ - y 0)) (P t)
        (y i.succ - y 0) =
      (∫ s in Δ q, ω (y 1 + ∑ j, s j • (y j.succ.succ - y 1)) (i.removeNth fun j => y j.succ - y 0)) -
        I ω (fun j => y (i.succ.succAbove j)) := by
    intro i
    set r : Fin q → V := i.removeNth fun j => y j.succ - y 0 with hr
    have hder : ∀ t ∈ P ⁻¹' U, HasDerivAt (fun x => ω (P (Function.update t i x)) r)
        (fderiv ℝ (fun z => ω z r) (P t) (y i.succ - y 0)) (t i) := by
      intro t ht
      have hx : HasDerivAt (fun x => P (Function.update t i x)) (y i.succ - y 0) (t i) := by
        have he : (fun x => P (Function.update t i x)) = fun x => P t + (x - t i) • (y i.succ - y 0) := by
          funext x
          exact P_update y t i x
        rw [he]
        simpa using (((hasDerivAt_id (t i)).sub_const (t i)).smul_const (y i.succ - y 0)).const_add (P t)
      exact (hφd r (P t) ht).comp_hasDerivAt_of_eq (t i) hx (by simp)
    have h := hS q i (fun t => ω (P t) r) (fun t => fderiv ℝ (fun z => ω z r) (P t) (y i.succ - y 0))
      (P ⁻¹' U) hW hΔW ((hφc r).comp hPc.continuousOn (fun t ht => ht))
      (((hφdc r).comp hPc.continuousOn (fun t ht => ht)).clm_apply continuousOn_const) hder
    rw [h, hH q (fun t => ω (P t) r) i]
    congr 1
    · congr 1
      funext s
      simp only [hP]
      rw [P_cons]
    · simp only [I]
      congr 1
      funext s
      simp only [hP]
      rw [P_insertNth, zero_smul, add_zero]
      simp only [Fin.succ_succAbove_zero, Fin.succ_succAbove_succ, hr]
      rfl
  have hext : Set.EqOn (fun t => extDeriv ω (P t) (fun j => y j.succ - y 0))
      (fun t => ∑ i : Fin (q + 1), (-1 : ℝ) ^ (i : ℕ) *
        fderiv ℝ (fun z => ω z (i.removeNth fun j => y j.succ - y 0)) (P t) (y i.succ - y 0))
      (Δ (q + 1)) := by
    intro t ht
    show extDeriv ω (P t) (fun j => y j.succ - y 0) = _
    rw [extDeriv_apply ((hω.differentiableOn one_ne_zero _ (hΔW ht)).differentiableAt
      (hU.mem_nhds (hΔW ht))) (fun j => y j.succ - y 0)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [zsmul_eq_mul]
    push_cast
    rfl
  have hR : I (extDeriv ω) y = ∑ i : Fin (q + 1), (-1 : ℝ) ^ (i : ℕ) *
      ∫ t in Δ (q + 1), fderiv ℝ (fun z => ω z (i.removeNth fun j => y j.succ - y 0)) (P t)
        (y i.succ - y 0) := by
    show ∫ t in Δ (q + 1), extDeriv ω (P t) (fun j => y j.succ - y 0) = _
    rw [setIntegral_congr_fun (hmeas _) hext, integral_finset_sum]
    · congr 1
      funext i
      rw [← integral_const_mul]
    · intro i _
      have hc := (((hφdc (i.removeNth fun j => y j.succ - y 0)).comp hPc.continuousOn
        (fun t ht => ht)).clm_apply (continuousOn_const (c := y i.succ - y 0))).mono hΔW
      exact (continuousOn_const.mul hc).integrableOn_compact (isCompact_Δ' _)
  have hface0 : I ω (fun j => y ((0 : Fin (q + 2)).succAbove j)) = ∑ i : Fin (q + 1), (-1 : ℝ) ^ (i : ℕ) *
      ∫ s in Δ q, ω (y 1 + ∑ j, s j • (y j.succ.succ - y 1)) (i.removeNth fun j => y j.succ - y 0) := by
    have hQ : ∀ s ∈ Δ q, y 1 + ∑ j, s j • (y j.succ.succ - y 1) ∈ U := fun s hs =>
      hmem q (fun j => y j.succ) (fun j => hy _) s hs
    have e1 : I ω (fun j => y ((0 : Fin (q + 2)).succAbove j)) = ∫ s in Δ q, ∑ i : Fin (q + 1),
        (-1 : ℝ) ^ (i : ℕ) * ω (y 1 + ∑ j, s j • (y j.succ.succ - y 1)) (i.removeNth fun j => y j.succ - y 0) := by
      simp only [I, Fin.succAbove_zero, Fin.succ_zero_eq_one]
      congr 1
      funext s
      rw [← hA V q]
      congr 1
      funext j
      simp only [Fin.succ_zero_eq_one, sub_sub_sub_cancel_right]
    rw [e1, integral_finset_sum]
    · congr 1
      funext i
      rw [integral_const_mul]
    · intro i _
      have hc : ContinuousOn (fun s : Fin q → ℝ => y 1 + ∑ j, s j • (y j.succ.succ - y 1)) (Δ q) :=
        (continuous_const.add (continuous_finset_sum _ fun j _ =>
          (continuous_apply j).smul continuous_const)).continuousOn
      exact (continuousOn_const.mul ((hφc (i.removeNth fun j => y j.succ - y 0)).comp hc hQ)).integrableOn_compact (isCompact_Δ' _)
  rw [hR, Fin.sum_univ_succ]
  simp only [hslice, mul_sub, Finset.sum_sub_distrib, ← hface0, Fin.val_zero, pow_zero, one_mul,
    Fin.val_succ, pow_succ, mul_neg, mul_one, neg_mul, Finset.sum_neg_distrib]
  ring

end PositivityTheory.KB.StokesSlices
