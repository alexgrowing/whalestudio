import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem tr_one {R : Type} [CommRing R] {a : ℕ} (A B Z : Matrix (Fin a) (Fin a) R) :
    (A * (Z * B - B * Z)).trace = -(B * (Z * A - A * Z)).trace := by
  have h1 : (A * (Z * B)).trace = (B * (A * Z)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have h2 : (B * (Z * A)).trace = (A * (B * Z)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_sub, Matrix.trace_sub, h1, h2]
  ring

private theorem trF_one {E : Type} [Field E] [NumberField E] {a : ℕ} (A B Z : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF A (Z * B - B * Z) = -trF B (Z * A - A * Z) := by
  unfold trF
  rw [tr_one, ← Finset.sum_neg_distrib]
  rfl

private theorem trF_neg {E : Type} [Field E] [NumberField E] {a : ℕ} (A B : Matrix (Fin a) (Fin a) (Cinf E)) :
    trF A (-B) = -trF A B := by
  unfold trF
  rw [Matrix.mul_neg, Matrix.trace_neg, ← Finset.sum_neg_distrib]
  rfl

theorem UpperTheory.V.Lit.Bor.frameBr :
    UpperTheory.V.Lit.Bor.FrameBr := by
  intro E _ _ _ a n e he N _ _
  refine ⟨fun β Z hZ => ?_, fun β X h => ?_⟩
  · have h1 : ∀ j, β (brH Z hZ (e j)) (e j) = ∑ k, trF (e k).1 (Z * (e j).1 - (e j).1 * Z) • β (e k) (e j) := by
      intro j
      conv_lhs => rw [he (brH Z hZ (e j))]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      rfl
    have h2 : ∀ j, β (e j) (brH Z hZ (e j)) = ∑ k, trF (e k).1 (Z * (e j).1 - (e j).1 * Z) • β (e j) (e k) := by
      intro j
      conv_lhs => rw [he (brH Z hZ (e j))]
      simp only [map_sum, map_smul]
      rfl
    simp only [h1, h2]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [trF_one, neg_smul, neg_add_cancel]
  · have hb : ∀ j, (brH _ (h j) X).1 = -((Complex.I • X.1) * (e j).1 - (e j).1 * (Complex.I • X.1)) := by
      intro j
      change (Complex.I • (e j).1) * X.1 - X.1 * (Complex.I • (e j).1) = _
      simp only [Matrix.smul_mul, Matrix.mul_smul, neg_sub]
    have h1 : ∀ j, X.1 * (e j).1 - (e j).1 * X.1 =
        ∑ k, trF (e k).1 (brH _ (h j) X).1 • (Complex.I • (e k).1) := by
      intro j
      have h0 : (brH _ (h j) X).1 = ∑ k, trF (e k).1 (brH _ (h j) X).1 • (e k).1 := by
        conv_lhs => rw [he (brH _ (h j) X)]
        simp only [Submodule.coe_sum, Submodule.coe_smul]
      have h3 : X.1 * (e j).1 - (e j).1 * X.1 = Complex.I • (brH _ (h j) X).1 := by
        rw [hb]
        simp only [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, smul_neg, smul_smul, Complex.I_mul_I, neg_smul,
          one_smul, neg_neg]
      rw [h3]
      conv_lhs => rw [h0]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    have h2 : ∀ j, β (Complex.I • (e j).1) (brH _ (h j) X) =
        ∑ k, trF (e k).1 (brH _ (h j) X).1 • β (Complex.I • (e j).1) (e k) := by
      intro j
      conv_lhs => rw [he (brH _ (h j) X)]
      simp only [map_sum, map_smul]
    simp only [h1, h2]
    simp only [map_sum, LinearMap.map_smul β, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hb, hb, trF_neg, trF_neg, trF_one, neg_smul]
