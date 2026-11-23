import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace cubicPeriodConstant

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem blkU_low {j : ℕ} (x : UnipotentBlockColumnIndex k j j → Ad E) (i c : Fin k) (h : c ≤ i) :
    (blkU x : GA E k).val i c = (1 : Matrix (Fin k) (Fin k) (Ad E)) i c := by
  have h' : (c : ℕ) ≤ i := h
  change (1 + posM Subtype.val x : Matrix (Fin k) (Fin k) (Ad E)) i c = _
  rw [Matrix.add_apply, posM, Matrix.sum_apply, Finset.sum_eq_zero, add_zero]
  intro t _
  have h1 := t.2
  rw [Matrix.single_apply_of_ne]
  rintro ⟨e1, e2⟩
  rw [← e1, ← e2] at h'
  omega

theorem blkU_unipotent_zero {j : ℕ} (x : UnipotentBlockColumnIndex k j j → Ad E) : UU 0 (blkU x : GA E k) := by
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [blkU_low x i c h.le, Matrix.one_apply_ne (ne_of_gt h)]
  · rw [blkU_low x i i le_rfl, Matrix.one_apply_eq]

theorem unipotent_zero_one : UU 0 (1 : GA E k) := by
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [Units.val_one, Matrix.one_apply_ne (ne_of_gt h)]
  · rw [Units.val_one, Matrix.one_apply_eq]

theorem unipotent_zero_mul {u v : GA E k} (hu : UU 0 u) (hv : UU 0 v) : UU 0 (u * v) := by
  refine ⟨fun i c h => ?_, fun i => ?_, fun i c h => absurd h (Nat.not_lt_zero _)⟩
  · rw [Units.val_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with hl | hl
    · rw [hu.1 i l hl, zero_mul]
    · rw [hv.1 l c (lt_of_lt_of_le h hl), mul_zero]
  · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hu.2.1, hv.2.1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with hl | hl
      · rw [hu.1 i l hl, zero_mul]
      · rw [hv.1 l i hl, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi

theorem step (ψ : AddChar (Ad E) ℂ) (j : ℕ) (f f' : GA E k → ℂ) (g g' : GA E k) (c : ℂ)
    (h : ∀ u, UU 0 u → f (u * g) = c * f' (u * g')) :
    ∀ u, UU 0 u → colT ψ j f (u * g) = c * colT ψ j f' (u * g') := by
  intro u hu
  simp only [colT, coefF]
  rw [← avg_const_mul]
  congr 1
  funext x
  rw [← mul_assoc (blkU x) u g, ← mul_assoc (blkU x) u g', h _ (unipotent_zero_mul (blkU_unipotent_zero x) hu)]
  ring

theorem whit_gen (ψ : AddChar (Ad E) ℂ) (g g' : GA E k) : ∀ (m : ℕ) (f f' : GA E k → ℂ) (c : ℂ),
    (∀ u, UU 0 u → f (u * g) = c * f' (u * g')) →
      ∀ u, UU 0 u → whit ψ m f (u * g) = c * whit ψ m f' (u * g')
  | 0, _, _, _, h => h
  | m + 1, f, f', c, h => whit_gen ψ g g' m _ _ c (step ψ (m + 1) f f' g g' c h)

end cubicPeriodConstant

theorem crystalline_clause_of_admitted : P3 := by
  intro E _ _ _ k ψ m f f' g g' c h
  simpa only [one_mul] using cubicPeriodConstant.whit_gen ψ g g' m f f' c h 1 cubicPeriodConstant.unipotent_zero_one

end PositivityTheory.AdelicQuotientData

end
