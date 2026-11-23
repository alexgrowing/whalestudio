import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CjDefs

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open MeasureTheory

def IsLowUni {A : Type} [CommRing A] {k : ℕ} (U : Matrix (Fin k) (Fin k) A) : Prop :=
  (∀ i, U i i = 1) ∧ ∀ i j : Fin k, i < j → U i j = 0

theorem mulVec_succAbove_step {A : Type} [CommRing A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [MeasurableMul₂ A] (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] {k : ℕ}
    (U : Matrix (Fin (k + 1)) (Fin (k + 1)) A) (p : Fin (k + 1)) (hpp : U p p = 1)
    (hp : ∀ i, U (p.succAbove i) p = 0)
    (hIH : MeasurePreserving (U.submatrix p.succAbove p.succAbove).mulVec
      (Measure.pi fun _ : Fin k => ν) (Measure.pi fun _ : Fin k => ν)) :
    MeasurePreserving U.mulVec (Measure.pi fun _ : Fin (k + 1) => ν)
      (Measure.pi fun _ : Fin (k + 1) => ν) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => A) p with he
  have he_mp : MeasurePreserving e (Measure.pi fun _ : Fin (k + 1) => ν)
      (ν.prod (Measure.pi fun _ : Fin k => ν)) :=
    measurePreserving_piFinSuccAbove (fun _ => ν) p
  set U' := U.submatrix p.succAbove p.succAbove with hU'
  set r : (Fin k → A) → A := fun v => ∑ i, U p (p.succAbove i) * v i with hr
  have hrm : Measurable r :=
    Finset.measurable_sum _ fun i _ => measurable_const.mul (measurable_pi_apply i)
  have hskew : MeasurePreserving (fun z : (Fin k → A) × A => (U'.mulVec z.1, r z.1 + z.2))
      ((Measure.pi fun _ : Fin k => ν).prod ν) ((Measure.pi fun _ : Fin k => ν).prod ν) :=
    hIH.skew_product (g := fun v a => r v + a) ((hrm.comp measurable_fst).add measurable_snd)
      (Filter.Eventually.of_forall fun v => map_add_left_eq_self ν (r v))
  have hT : MeasurePreserving (fun z : A × (Fin k → A) => (r z.2 + z.1, U'.mulVec z.2))
      (ν.prod (Measure.pi fun _ : Fin k => ν)) (ν.prod (Measure.pi fun _ : Fin k => ν)) :=
    (Measure.measurePreserving_swap.comp hskew).comp Measure.measurePreserving_swap
  have hmul : U.mulVec = e.symm ∘ (fun z : A × (Fin k → A) => (r z.2 + z.1, U'.mulVec z.2)) ∘ e := by
    funext x
    apply e.injective
    simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    have hex : ∀ y : Fin (k + 1) → A, e y = (y p, fun i => y (p.succAbove i)) := fun y => rfl
    rw [hex, hex]
    refine Prod.ext ?_ ?_
    · show (∑ j, U p j * x j) = r (fun i => x (p.succAbove i)) + x p
      rw [Fin.sum_univ_succAbove _ p, hpp, one_mul, add_comm]
    · funext i
      show (∑ j, U (p.succAbove i) j * x j) = ∑ j, U' i j * x (p.succAbove j)
      rw [Fin.sum_univ_succAbove _ p, hp i, zero_mul, zero_add]
      rfl
  rw [hmul]
  exact (MeasurePreserving.symm e he_mp).comp (hT.comp he_mp)

theorem uni_measurePreserving {A : Type} [CommRing A] [MeasurableSpace A] [MeasurableAdd₂ A]
    [MeasurableMul₂ A] (ν : Measure A) [SigmaFinite ν] [ν.IsAddLeftInvariant] :
    ∀ (k : ℕ) (U : Matrix (Fin k) (Fin k) A), (IsLowUni U ∨ IsLowUni U.transpose) →
      MeasurePreserving U.mulVec (Measure.pi fun _ : Fin k => ν)
        (Measure.pi fun _ : Fin k => ν) := by
  intro k
  induction k with
  | zero =>
    intro U _
    have h0 : U.mulVec = id := by
      funext x i
      exact i.elim0
    rw [h0]
    exact MeasurePreserving.id _
  | succ k ih =>
    intro U hU
    rcases hU with hL | hT
    · refine mulVec_succAbove_step ν U (Fin.last k) (hL.1 _) (fun i => ?_)
        (ih _ (Or.inl ⟨fun a => ?_, fun a b hab => ?_⟩))
      · rw [Fin.succAbove_last]
        exact hL.2 _ _ (Fin.castSucc_lt_last i)
      · simp only [Matrix.submatrix_apply, Fin.succAbove_last]
        exact hL.1 _
      · simp only [Matrix.submatrix_apply, Fin.succAbove_last]
        exact hL.2 _ _ (Fin.castSucc_lt_castSucc_iff.mpr hab)
    · refine mulVec_succAbove_step ν U 0 (hT.1 0) (fun i => ?_)
        (ih _ (Or.inr ⟨fun a => ?_, fun a b hab => ?_⟩))
      · rw [Fin.succAbove_zero]
        exact hT.2 0 i.succ (Fin.succ_pos i)
      · simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Fin.succAbove_zero]
        exact hT.1 _
      · simp only [Matrix.transpose_apply, Matrix.submatrix_apply, Fin.succAbove_zero]
        exact hT.2 _ _ (Fin.succ_lt_succ_iff.mpr hab)

theorem uni_haar {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A]
    [BorelSpace A] (k : ℕ) (U : Matrix (Fin k) (Fin k) A) (hU : IsLowUni U ∨ IsLowUni U.transpose)
    (μ : Measure (Fin k → A)) [μ.IsAddHaarMeasure] : μ.map U.mulVec = μ := by
  have hpi : (Measure.pi fun _ : Fin k => (Measure.addHaar : Measure A)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  rw [Measure.isAddLeftInvariant_eq_smul μ (Measure.pi fun _ : Fin k => (Measure.addHaar : Measure A)),
    Measure.map_smul, (uni_measurePreserving (Measure.addHaar : Measure A) k U hU).map_eq]

theorem transvection_uni {A : Type} [CommRing A] {k : ℕ} (i j : Fin k) (hij : i ≠ j) (c : A) :
    IsLowUni (Matrix.transvection i j c) ∨ IsLowUni (Matrix.transvection i j c).transpose := by
  have key : ∀ a b : Fin k, (i = a ∧ j = b → False) → Matrix.single i j c a b = 0 := fun a b h => by
    rw [Matrix.single_apply, if_neg (fun hh => h hh)]
  have tac : ∀ a b : Fin k, (a < b ∧ i = a ∧ j = b → False) ∨ True := fun _ _ => Or.inr trivial
  rcases lt_or_gt_of_ne hij with h | h
  · right
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · simp only [Matrix.transvection, Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply_eq]
      rw [key a a (fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)), add_zero]
    · simp only [Matrix.transvection, Matrix.transpose_apply, Matrix.add_apply]
      rw [Matrix.one_apply_ne (ne_of_gt hab), key b a (fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (lt_trans h hab) (lt_irrefl _)), add_zero]
  · left
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_eq]
      rw [key a a (fun ⟨h1, h2⟩ => hij (h1.trans h2.symm)), add_zero]
    · simp only [Matrix.transvection, Matrix.add_apply]
      rw [Matrix.one_apply_ne (ne_of_lt hab), key a b (fun ⟨h1, h2⟩ => by
        subst h1; subst h2; exact absurd (lt_trans h hab) (lt_irrefl _)), add_zero]

theorem transvection_preserves_haar : TransvHaar := by
  intro A _ _ _ _ _ _ _ _ k i j hij c μ hμ
  haveI := hμ
  exact uni_haar k _ (transvection_uni i j hij c) μ

end PI.VolSemiDirect.W.Cj
