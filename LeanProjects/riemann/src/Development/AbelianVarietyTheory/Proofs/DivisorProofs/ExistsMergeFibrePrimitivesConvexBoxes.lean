import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticParamOfPrimitivesOnBox
open Set

namespace GlobalTheory

open Set in

theorem _root_.GlobalTheory.exists_merge_fibre_primitives : ∀ {P : Type} [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P] {g : ℕ} {K : Type} (W : K → Set (P × (Fin g → ℂ))) (c : K → K → P × (Fin g → ℂ) → ℂ) (ω : K → Fin g → P × (Fin g → ℂ) → ℂ) (Z : Set P) (C : Set (Fin g → ℂ)) (C' : Set (Fin g → ℂ)) (G G' : K → P × (Fin g → ℂ) → ℂ), (∀ k, IsOpen (W k)) → IsOpen Z → IsOpen C → Convex ℝ C → IsOpen C' → Convex ℝ C' → (C ∩ C').Nonempty → (∀ p ∈ Z ×ˢ (C ∪ C'), ∃ k, p ∈ W k) → ((∀ k, AnalyticOnNhd ℂ (G k) (W k ∩ Z ×ˢ C)) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C → fderiv ℂ (G k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C → G k p - G l p = c k l p) → ((∀ k, AnalyticOnNhd ℂ (G' k) (W k ∩ Z ×ˢ C')) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ C' → fderiv ℂ (G' k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ C' → G' k p - G' l p = c k l p) → ∃ G'' : K → P × (Fin g → ℂ) → ℂ, ((∀ k, AnalyticOnNhd ℂ (G'' k) (W k ∩ Z ×ˢ (C ∪ C'))) ∧ (∀ k a, ∀ p ∈ W k, p ∈ Z ×ˢ (C ∪ C') → fderiv ℂ (G'' k) p (0, Pi.single a 1) = ω k a p) ∧ ∀ k l, ∀ p ∈ W k, p ∈ W l → p ∈ Z ×ˢ (C ∪ C') → G'' k p - G'' l p = c k l p) := by
  intro P _ _ _ g K W c ω Z C C' G G' hW hZ hC hCc hC' hC'c hne hcov ⟨hGa, hGd, hGc⟩
    ⟨hG'a, hG'd, hG'c⟩
  have hsubC : Z ×ˢ (C ∩ C') ⊆ Z ×ˢ C := prod_mono subset_rfl inter_subset_left
  have hsubC' : Z ×ˢ (C ∩ C') ⊆ Z ×ˢ C' := prod_mono subset_rfl inter_subset_right
  obtain ⟨h, hh, hGG⟩ := _root_.GlobalTheory.exists_analytic_param_of_primitives_on_box W c ω Z (C ∩ C') G G' hW hZ
    (hC.inter hC') (hCc.inter hC'c) hne
    (fun p hp => hcov p (prod_mono subset_rfl subset_union_left (hsubC hp)))
    ⟨fun k => (hGa k).mono (inter_subset_inter_right _ hsubC),
      fun k a p hpk hp => hGd k a p hpk (hsubC hp),
      fun k l p hk hl hp => hGc k l p hk hl (hsubC hp)⟩
    ⟨fun k => (hG'a k).mono (inter_subset_inter_right _ hsubC'),
      fun k a p hpk hp => hG'd k a p hpk (hsubC' hp),
      fun k l p hk hl hp => hG'c k l p hk hl (hsubC' hp)⟩
  classical
  have hCeq : ∀ k, ∀ q ∈ W k ∩ Z ×ˢ C,
      (if q.2 ∈ C then G k q else G' k q + h q.1) = G k q := fun k q hq => if_pos hq.2.2
  have hC'eq : ∀ k, ∀ q ∈ W k ∩ Z ×ˢ C',
      (if q.2 ∈ C then G k q else G' k q + h q.1) = G' k q + h q.1 := by
    intro k q hq
    split_ifs with hqC
    · exact hGG k q hq.1 ⟨hq.2.1, hqC, hq.2.2⟩
    · rfl
  have hU : ∀ k, IsOpen (W k ∩ Z ×ˢ C) := fun k => (hW k).inter (hZ.prod hC)
  have hU' : ∀ k, IsOpen (W k ∩ Z ×ˢ C') := fun k => (hW k).inter (hZ.prod hC')
  have evC : ∀ k, ∀ p ∈ W k ∩ Z ×ˢ C,
      (fun q => if q.2 ∈ C then G k q else G' k q + h q.1) =ᶠ[nhds p] G k :=
    fun k p hp => Filter.eventually_of_mem ((hU k).mem_nhds hp) (hCeq k)
  have evC' : ∀ k, ∀ p ∈ W k ∩ Z ×ˢ C',
      (fun q => if q.2 ∈ C then G k q else G' k q + h q.1) =ᶠ[nhds p]
        fun q => G' k q + h q.1 :=
    fun k p hp => Filter.eventually_of_mem ((hU' k).mem_nhds hp) (hC'eq k)
  have memcase : ∀ p ∈ Z ×ˢ (C ∪ C'), p ∈ Z ×ˢ C ∨ p ∈ Z ×ˢ C' := fun p hp =>
    hp.2.elim (fun h1 => Or.inl ⟨hp.1, h1⟩) (fun h2 => Or.inr ⟨hp.1, h2⟩)
  have hfd : ∀ k, ∀ p ∈ W k ∩ Z ×ˢ C', HasFDerivAt (fun q => G' k q + h q.1)
      (fderiv ℂ (G' k) p + (fderiv ℂ h p.1).comp (ContinuousLinearMap.fst ℂ P (Fin g → ℂ))) p :=
    fun k p hp => (hG'a k p hp).differentiableAt.hasFDerivAt.add
      ((hh p.1 hp.2.1).differentiableAt.hasFDerivAt.comp p (hasFDerivAt_fst))
  refine ⟨fun k => (fun k p => if p.2 ∈ C then G k p else G' k p + h p.1) k, ?_⟩
  refine ⟨fun k p hp => ?_, fun k a p hpk hp => ?_, fun k l p hk hl hp => ?_⟩
  · dsimp only
    rcases memcase p hp.2 with h1 | h2
    · exact (hGa k p ⟨hp.1, h1⟩).congr (evC k p ⟨hp.1, h1⟩).symm
    · exact (hfd k p ⟨hp.1, h2⟩).differentiableAt |> fun _ =>
        ((hG'a k p ⟨hp.1, h2⟩).add ((hh p.1 h2.1).comp analyticAt_fst)).congr
          (evC' k p ⟨hp.1, h2⟩).symm
  · dsimp only
    rcases memcase p hp with h1 | h2
    · rw [(evC k p ⟨hpk, h1⟩).fderiv_eq]
      exact hGd k a p hpk h1
    · rw [(evC' k p ⟨hpk, h2⟩).fderiv_eq, (hfd k p ⟨hpk, h2⟩).fderiv,
        ContinuousLinearMap.add_apply, hG'd k a p hpk h2]
      simp
  · dsimp only
    rcases memcase p hp with h1 | h2
    · rw [if_pos h1.2, if_pos h1.2]
      exact hGc k l p hk hl h1
    · rw [hC'eq k p ⟨hk, h2⟩, hC'eq l p ⟨hl, h2⟩, add_sub_add_right_eq_sub]
      exact hG'c k l p hk hl h2

end GlobalTheory
