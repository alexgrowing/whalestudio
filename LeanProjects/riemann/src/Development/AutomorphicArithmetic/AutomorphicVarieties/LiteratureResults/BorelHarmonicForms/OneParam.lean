import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.KCurve
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpMat
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem op_cont_inf (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

open scoped Matrix.Norms.Operator in
private theorem exists_one_parameter_exp {E : Type} [Field E] [NumberField E] {a : ℕ} (Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ Continuous c ∧
      HasDerivAt (fun t => toL (c t).val) (toL Y) 0 ∧ ∀ t : ℝ, (c t).val = NormedSpace.exp (t • Y) := by
  let c : ℝ → GL (Fin a) (Cinf E) := fun t => (Matrix.isUnit_exp (t • Y)).unit
  have hc : ∀ t, (c t).val = NormedSpace.exp (t • Y) := fun t => rfl
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hadd : ∀ s t, c (s + t) = c s * c t := fun s t => Units.ext (by
    rw [Units.val_mul, hc, hc, hc, add_smul,
      Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left s).smul_right t)])
  have hv : Continuous fun t : ℝ => NormedSpace.exp (t • Y) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y t).continuousAt
  have hinv : ∀ t, (c t)⁻¹ = c (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  refine ⟨c, h0, hadd, Units.continuous_iff.2 ⟨hv, ?_⟩, ?_, hc⟩
  · simp only [hinv, hc]
    exact hv.comp continuous_neg
  · have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h

theorem UpperTheory.V.Lit.Bor.oneParam :
    UpperTheory.V.Lit.Bor.OneParam := by
  intro E _ _ _ a X
  obtain ⟨c, h0, hadd, hc, hd, he⟩ := exists_one_parameter_exp (E := E) (Matrix.of X)
  exact ⟨c, h0, hadd, (op_cont_inf E a).comp hc, hd, he⟩
