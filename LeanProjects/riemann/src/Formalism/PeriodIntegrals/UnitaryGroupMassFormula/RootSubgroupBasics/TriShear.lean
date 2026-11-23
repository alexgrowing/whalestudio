import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RootSubgroupBasics.TriDefs

open MeasureTheory

noncomputable section

namespace PI.AmpRootCommon.Tri

def extNe {ι : Type} [DecidableEq ι] (a : ι) (y : {i // i ≠ a} → ℂ) : ι → ℂ :=
  fun j => if h : j ≠ a then y ⟨j, h⟩ else 0

theorem measurable_extNe {ι : Type} [DecidableEq ι] (a : ι) : Measurable (extNe a) := by
  refine measurable_pi_lambda _ (fun j => ?_)
  by_cases h : j ≠ a
  · simp only [extNe, dif_pos h]
    exact measurable_pi_apply _
  · simp only [extNe, dif_neg h]
    exact measurable_const

theorem measurePreserving_of_card (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (r : ι → ℕ) (g : ι → (ι → ℂ) → ℂ), (∀ i, Measurable (g i)) →
    (∀ i (x y : ι → ℂ), (∀ j, r j < r i → x j = y j) → g i x = g i y) →
    MeasurePreserving (fun x : ι → ℂ => fun i => x i + g i x) volume volume := by
  induction n with
  | zero =>
    intro ι _ _ hcard r g hg hdep
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    have hid : (fun x : ι → ℂ => fun i => x i + g i x) = id :=
      funext fun x => funext fun i => isEmptyElim i
    rw [hid]
    exact MeasurePreserving.id _
  | succ n ih =>
    intro ι _ _ hcard r g hg hdep
    have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    obtain ⟨a, ha⟩ := Finite.exists_max r
    have hcard' : Fintype.card {i // i ≠ a} = n := by
      rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ a),
        Finset.card_univ, hcard]
      rfl
    have hext : ∀ i (x : ι → ℂ), g i x = g i (extNe a (fun j : {j // j ≠ a} => x j.1)) := by
      intro i x
      apply hdep i
      intro j hj
      by_cases hja : j ≠ a
      · simp only [extNe, dif_pos hja]
      · have hja' : j = a := not_not.mp hja
        rw [hja'] at hj
        have := ha i
        omega
    have hT := ih {i // i ≠ a} hcard' (fun i => r i.1)
      (fun i y => g i.1 (extNe a y))
      (fun i => (hg i.1).comp (measurable_extNe a))
      (fun i y y' hyy' => hdep i.1 _ _ (fun j hj => by
        by_cases hja : j ≠ a
        · simp only [extNe, dif_pos hja]
          exact hyy' ⟨j, hja⟩ hj
        · simp only [extNe, dif_neg hja]))
    have hc : Measurable (fun (y : {i // i ≠ a} → ℂ) (_ : {i // ¬ i ≠ a}) => g a (extNe a y)) :=
      measurable_pi_lambda _ fun _ => (hg a).comp (measurable_extNe a)
    have hS : MeasurePreserving
        (fun p : ({i // i ≠ a} → ℂ) × ({i // ¬ i ≠ a} → ℂ) =>
          ((fun i => p.1 i + g i.1 (extNe a p.1)),
            p.2 + fun (_ : {i // ¬ i ≠ a}) => g a (extNe a p.1))) volume volume :=
      hT.skew_product (g := fun y z => z + fun (_ : {i // ¬ i ≠ a}) => g a (extNe a y))
        (measurable_snd.add (hc.comp measurable_fst))
        (ae_of_all _ fun y => map_add_right_eq_self volume _)
    have hΦ := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun i => i ≠ a)
    have hF : (fun x : ι → ℂ => fun i => x i + g i x) =
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun i => i ≠ a)).symm ∘
          (fun p : ({i // i ≠ a} → ℂ) × ({i // ¬ i ≠ a} → ℂ) =>
            ((fun i => p.1 i + g i.1 (extNe a p.1)),
              p.2 + fun (_ : {i // ¬ i ≠ a}) => g a (extNe a p.1))) ∘
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun i => i ≠ a)) := by
      funext x i
      show x i + g i x = (if h : i ≠ a then _ else _)
      by_cases hi : i ≠ a
      · rw [dif_pos hi]
        show x i + g i x = x i + g i (extNe a (fun j : {j // j ≠ a} => x j.1))
        rw [← hext i x]
      · rw [dif_neg hi]
        show x i + g i x = x i + g a (extNe a (fun j : {j // j ≠ a} => x j.1))
        have hia : i = a := not_not.mp hi
        rw [hia, ← hext a x]
    rw [hF]
    exact (MeasurePreserving.symm _ hΦ).comp (hS.comp hΦ)

theorem triShear : TriShear :=
  fun ι _ _ r g hg hdep => measurePreserving_of_card (Fintype.card ι) ι rfl r g hg hdep

end PI.AmpRootCommon.Tri
