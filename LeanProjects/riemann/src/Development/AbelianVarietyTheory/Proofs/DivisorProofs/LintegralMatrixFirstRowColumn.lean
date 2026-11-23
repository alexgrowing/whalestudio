import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.KSplit.CornerFubini

theorem lintegral_prod_le_symm {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] (f : α × β → ℝ≥0∞) :
    ∫⁻ z, f z ∂(μ.prod ν) ≤ ∫⁻ y, ∫⁻ x, f (x, y) ∂μ ∂ν := by
  rw [← lintegral_prod_swap]
  exact lintegral_prod_le _

theorem lintegral_cons_le {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (n : ℕ)
    (G : (Fin (n + 1) → α) → ℝ≥0∞) :
    ∫⁻ X, G X ∂(Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ∫⁻ u, ∫⁻ x, G (Fin.cons x u) ∂μ ∂(Measure.pi fun _ : Fin n => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  rw [h.lintegral_map_equiv G _]
  refine (lintegral_prod_le_symm _ _ _).trans (le_of_eq ?_)
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem lintegral_col_le {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (m n : ℕ)
    (G : (Fin m → Fin (n + 1) → α) → ℝ≥0∞) :
    ∫⁻ X, G X ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (n + 1) => μ) ≤
      ∫⁻ M, ∫⁻ v, G (fun i => Fin.cons (v i) (M i)) ∂(Measure.pi fun _ : Fin m => μ)
        ∂(Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin n => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0).symm
  have h1 : MeasurePreserving (MeasurableEquiv.piCongrRight fun _ : Fin m => e)
      (Measure.pi fun _ : Fin m => μ.prod (Measure.pi fun _ : Fin n => μ))
      (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin (n + 1) => μ) :=
    measurePreserving_pi _ _ (f := fun _ : Fin m => e) (fun _ => h)
  have h2 := (measurePreserving_arrowProdEquivProdArrow α (Fin n → α) (Fin m) (fun _ => μ)
    (fun _ => Measure.pi fun _ : Fin n => μ)).symm
  rw [h1.lintegral_map_equiv G _, h2.lintegral_map_equiv _ _]
  refine (lintegral_prod_le_symm _ _ _).trans (le_of_eq ?_)
  refine lintegral_congr fun M => lintegral_congr fun v => congrArg G ?_
  funext i
  change e (v i, M i) = _
  simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem lintegral_volM_le_corner (k : Type) [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν] (n : ℕ)
    (F : Matrix (Fin (n + 1)) (Fin (n + 1)) k → ℝ≥0∞) :
    ∫⁻ X, F X ∂(volM ν (Fin (n + 1)) (Fin (n + 1))) ≤
      ∫⁻ M, ∫⁻ v, ∫⁻ u, ∫⁻ x, F (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))
        ∂ν ∂(Measure.pi fun _ : Fin n => ν) ∂(Measure.pi fun _ : Fin n => ν) ∂(volM ν (Fin n) (Fin n)) := by
  refine (lintegral_cons_le (Measure.pi fun _ : Fin (n + 1) => ν) n F).trans ?_
  refine (lintegral_col_le ν n n _).trans ?_
  refine lintegral_mono fun M => lintegral_mono fun v => ?_
  exact lintegral_cons_le ν n
    (fun r => F (Matrix.of (Fin.cons r (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k)))))

end GlobalTheory.KSplit.CornerFubini
