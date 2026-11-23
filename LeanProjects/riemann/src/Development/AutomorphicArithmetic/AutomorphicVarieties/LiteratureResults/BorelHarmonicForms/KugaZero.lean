import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.kugaZero :
    UpperTheory.V.Lit.Bor.KugaZero := by
  intro E _ _ _ a n e M _ _ _ _ A B hc ω hω X
  rw [del_apply]
  simp only [cas, LinearMap.sub_apply, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs : star (Complex.I • (e j).1) = -(Complex.I • (e j).1) := by
    have h : star (e j).1 = (e j).1 := (e j).2
    rw [star_smul, h, Complex.star_def, Complex.conj_I, neg_smul]
  have h0 := hω _ hs X
  rw [Fin.sum_univ_zero, LinearMap.add_apply, LinearMap.add_apply] at h0
  have h1 : ∀ (Y Z) (m : M), A Y (B Z m) = B Z (A Y m) := fun Y Z m => LinearMap.congr_fun (hc Y Z).eq m
  have h2 := congrArg (B (toL (Complex.I • (e j).1))) h0
  have h3 := congrArg (A (toL (Complex.I • (e j).1))) h0
  rw [map_add, map_zero] at h2 h3
  rw [h1] at h3
  have h4 : B (toL (Complex.I • (e j).1)) (B (toL (Complex.I • (e j).1)) (ω X)) =
      A (toL (Complex.I • (e j).1)) (A (toL (Complex.I • (e j).1)) (ω X)) := by
    rw [← sub_eq_zero, ← sub_self (0 : M)]
    nth_rewrite 1 [← h2]
    rw [← h3]
    abel
  rw [dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) X]
  simp only [Fin.val_zero, pow_zero, one_smul, Matrix.cons_val_zero, LinearMap.add_apply, map_add, Module.End.mul_apply, h1, h4]
  abel
