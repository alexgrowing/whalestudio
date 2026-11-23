import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ActLPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.EvaluationSums.SuccAboveSuccEqCons

noncomputable section

namespace PositivityTheory.KB.ChainCochainPairing

variable {G : Type} [Group G]

def evh {m : ℕ} (Φ : (Fin (m + 1) → G) → ℝ) : Chn G m →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ fun g => Φ (Fin.partialProd g)

theorem evh_single {m : ℕ} (Φ : (Fin (m + 1) → G) → ℝ) (g : Fin m → G) (r : ℝ) :
    evh Φ (Finsupp.single g r) = r * Φ (Fin.partialProd g) := by
  simp [evh, Finsupp.linearCombination_single, smul_eq_mul]

theorem evh_eq_sum {m : ℕ} (Φ : (Fin (m + 1) → G) → ℝ) (z : Chn G m) :
    evh Φ z = z.sum fun g r => r * Φ (Fin.partialProd g) := by
  simp [evh, Finsupp.linearCombination_apply, smul_eq_mul]

theorem evh_sub {m : ℕ} (Φ Φ' : (Fin (m + 1) → G) → ℝ) (z : Chn G m) :
    evh (fun p => Φ p - Φ' p) z = evh Φ z - evh Φ' z := by
  simp only [evh_eq_sum, mul_sub, Finsupp.sum_sub]

theorem evh_zero {m : ℕ} (z : Chn G m) : evh (fun _ : Fin (m + 1) → G => (0 : ℝ)) z = 0 := by
  simp [evh_eq_sum]

theorem cob_eq_dC {Y : Type} {m : ℕ} (F : (Fin (m + 1) → Y) → ℝ) : cob F = dC F := rfl

theorem evh_bd {m : ℕ} (Φ : (Fin (m + 1) → G) → ℝ) (hΦ : ∀ (a : G) p, Φ (fun j => a * p j) = Φ p)
    (w : Chn G (m + 1)) : evh Φ (bd G m w) = evh (dC Φ) w := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single g r =>
    have h0 : (fun j => Fin.partialProd g ((0 : Fin (m + 2)).succAbove j)) =
        fun j => g 0 * Fin.partialProd (Fin.tail g) j := by
      funext j
      simp [Fin.partialProd_succ']
    have h1 : ∀ j : Fin (m + 1), (fun k => Fin.partialProd g ((Fin.succ j).succAbove k)) =
        Fin.partialProd (Fin.contractNth j (· * ·) g) := fun j => by
      rw [Fin.partialProd_contractNth]; rfl
    rw [evh_single, dC, Fin.sum_univ_succ, h0, hΦ]
    simp only [h1, bd, Finsupp.linearCombination_single, map_smul, map_add, map_sum, evh_single,
      smul_eq_mul, one_mul, Fin.val_zero, pow_zero, Fin.val_succ]
    rfl

end PositivityTheory.KB.ChainCochainPairing
