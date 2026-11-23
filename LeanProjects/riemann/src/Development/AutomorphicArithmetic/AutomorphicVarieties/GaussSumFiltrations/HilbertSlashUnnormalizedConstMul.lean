import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.SlashCocycle

open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F]

theorem cmp_det (v : InfinitePlace F) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((cmp v h).det : ℝ) = (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact (RingHom.map_det (Pi.evalRingHom (fun _ : InfinitePlace F => ℝ) v) _).symm

theorem det_mul_apply (v : InfinitePlace F) (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((h * h' : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v =
      (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v * (h' : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
  rw [← cmp_det, ← cmp_det, ← cmp_det, map_mul, map_mul, Units.val_mul]

theorem det_inv_apply (v : InfinitePlace F) (h : GL (Fin 2) (InfinitePlace F → ℝ)) :
    ((h⁻¹ : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v =
      ((h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v)⁻¹ := by
  rw [← cmp_det, ← cmp_det, map_inv, map_inv, Units.val_inv_eq_inv_val]

theorem denom_cmp_mul (v : InfinitePlace F) (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) (hh' : Pos h') (z : ℍ) :
    denom (cmp v h * cmp v h') z = denom (cmp v h) ((cmp v h' • z : ℍ) : ℂ) * denom (cmp v h') z := by
  have hp : 0 < ((cmp v h').det : ℝ) := by rw [cmp_det]; exact hh' v
  rw [denom_cocycle_σ, σ, if_pos hp]
  rfl

theorem act_mul (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) (z : Hn F) : act (h * h') z = act h (act h' z) := by
  funext v
  simp only [act, map_mul]
  exact mul_smul _ _ _

theorem act_one (z : Hn F) : act (1 : GL (Fin 2) (InfinitePlace F → ℝ)) z = z := by
  funext v
  simp only [act, map_one]
  exact one_smul _ _

theorem hilbertSlashUnnormalized_mul (k : ℕ) (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) (hh' : Pos h') (f : Hn F → ℂ) :
    sl0 k (h * h') f = sl0 k h' (sl0 k h f) := by
  funext z
  simp only [sl0, act_mul, map_mul]
  simp only [act, denom_cmp_mul _ h h' hh', Finset.prod_mul_distrib, mul_inv, mul_pow]
  ring

theorem hilbertSlashUnnormalized_one (k : ℕ) (f : Hn F → ℂ) : sl0 k 1 f = f := by
  funext z
  simp [sl0, act_one, denom_one]

theorem hilbertSlashUnnormalized_const_mul (k : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (c : ℂ) (f : Hn F → ℂ) (z : Hn F) :
    sl0 k h (fun w => c * f w) z = c * sl0 k h f z := by
  simp only [sl0]; ring

theorem slash_cocycle : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (h h' : GL (Fin 2) (InfinitePlace F → ℝ)) (f : Hn F → ℂ), Pos h → Pos h' → Pos (h * h') ∧ Pos h⁻¹ ∧ sl0 k (h * h') f = sl0 k h' (sl0 k h f) ∧ sl k (h * h') f = sl k h' (sl k h f) ∧ sl0 k 1 f = f ∧ sl k 1 f = f := by
  intro F _ _ k h h' f hh hh'
  refine ⟨fun v => ?_, fun v => ?_, hilbertSlashUnnormalized_mul k h h' hh' f, ?_, hilbertSlashUnnormalized_one k f, ?_⟩
  · rw [det_mul_apply]; exact mul_pos (hh v) (hh' v)
  · rw [det_inv_apply]; exact inv_pos.mpr (hh v)
  · funext z
    have hprod : (∏ v, |((h * h' : GL (Fin 2) (InfinitePlace F → ℝ)) : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) =
        (∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) *
          ∏ v, |(h' : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| := by
      simp only [det_mul_apply, abs_mul, Finset.prod_mul_distrib]
    have hsl : sl k h f = fun w => ((((∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v|) ^ ((k : ℝ) / 2) : ℝ) : ℂ)) * sl0 k h f w := rfl
    simp only [sl]
    rw [hsl, hilbertSlashUnnormalized_const_mul, hilbertSlashUnnormalized_mul k h h' hh' f, hprod,
      Real.mul_rpow (Finset.prod_nonneg fun v _ => abs_nonneg _) (Finset.prod_nonneg fun v _ => abs_nonneg _)]
    push_cast
    ring
  · funext z
    simp [sl, hilbertSlashUnnormalized_one]

end GlobalTheory.HilbertThetaSeries.SlashCocycle
