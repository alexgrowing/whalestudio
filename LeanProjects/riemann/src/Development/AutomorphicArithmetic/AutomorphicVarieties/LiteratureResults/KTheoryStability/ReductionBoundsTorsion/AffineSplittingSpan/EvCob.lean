import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.InclInj

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral

namespace EvaluationCoboundary

open PositivityTheory.KB

theorem ev_eq {G : Type} [Group G] {m : ℕ} (F : (Fin (m + 1) → G) → ℝ) (z : Chn G m) :
    ev (MonoidHom.id G) F 1 z =
      Finsupp.linearCombination ℝ (fun g : Fin m → G => F fun i => (MonoidHom.id G) (Fin.partialProd g i) • (1 : G)) z := by
  rw [Finsupp.linearCombination_apply]
  rfl

theorem key {G : Type} [Group G] (j : ℕ) (e : (Fin (j + 1) → G) → ℝ) (he : Inv (MonoidHom.id G) e)
    (g : Fin (j + 1) → G) :
    dC e (fun i => (MonoidHom.id G) (Fin.partialProd g i) • (1 : G)) =
      ev (MonoidHom.id G) e 1 (bd G j (Finsupp.single g 1)) := by
  rw [ev_eq, bd, Finsupp.linearCombination_single, one_smul, map_add, map_sum,
    Finsupp.linearCombination_single, dC, Fin.sum_univ_succ]
  simp only [MonoidHom.id_apply, smul_eq_mul, mul_one, Fin.succAbove_zero, one_smul,
    Fin.val_zero, pow_zero, one_mul, map_smul, Finsupp.linearCombination_single, Fin.val_succ]
  congr 1
  · have h := he (g 0) fun i => Fin.partialProd (fun i => g i.succ) i
    simp only [MonoidHom.id_apply, smul_eq_mul] at h
    rw [← h]
    congr 1
    funext i
    rw [Fin.partialProd_succ']
    rfl
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Fin.partialProd_contractNth]
    rfl

end EvaluationCoboundary

theorem evCob : EvCob := by
  intro G _ j e he z hz
  have h : ∀ w : Chn G (j + 1), ev (MonoidHom.id G) (dC e) 1 w =
      ev (MonoidHom.id G) e 1 (bd G j w) := by
    intro w
    induction w using Finsupp.induction_linear with
    | zero => simp [ev]
    | add a b ha hb =>
      rw [map_add, EvaluationCoboundary.ev_eq, map_add, ← EvaluationCoboundary.ev_eq, ← EvaluationCoboundary.ev_eq, ha, hb,
        EvaluationCoboundary.ev_eq, EvaluationCoboundary.ev_eq e (bd G j b), ← map_add, ← EvaluationCoboundary.ev_eq]
    | single g r =>
      rw [EvaluationCoboundary.ev_eq, Finsupp.linearCombination_single, EvaluationCoboundary.key j e he g,
        ← Finsupp.smul_single_one, map_smul, EvaluationCoboundary.ev_eq, EvaluationCoboundary.ev_eq, map_smul]
      rw [one_smul, ← map_smul, ← map_smul, Finsupp.smul_single_one]
  rw [h, hz]
  simp [ev]

end PositivityTheory.KB.SplitAffineSpectral

end
