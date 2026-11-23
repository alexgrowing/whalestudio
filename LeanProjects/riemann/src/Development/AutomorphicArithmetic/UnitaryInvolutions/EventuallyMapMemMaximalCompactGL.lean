import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

private lemma val_le_one_ae (E : Type) [Field E] [NumberField E] (e : E) :
    ∀ᶠ w : Pl E in cofinite, Valued.v (algebraMap E (w.adicCompletion E) e) ≤ 1 := by
  filter_upwards [(HeightOneSpectrum.Support.finite (𝓞 E) e).eventually_cofinite_notMem] with w hw
  have h : ¬ 1 < w.valuation E e := hw
  have h' : Valued.v (algebraMap E (w.adicCompletion E) e) = w.valuation E e :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w e
  rw [h']
  exact not_lt.mp h

private lemma mem_GLint {n : ℕ} {L : Type} [Field L] (O : Subring L) (g : GL (Fin n) L)
    (h₁ : ∀ i j, (g : Matrix (Fin n) (Fin n) L) i j ∈ O)
    (h₂ : ∀ i j, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ O) :
    g ∈ GLint (Fin n) O := by
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, h₁ i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨_, h₂ i j⟩
  have hA : A.map O.subtype = (g : Matrix (Fin n) (Fin n) L) := by
    ext i j; rfl
  have hB : B.map O.subtype = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    ext i j; rfl
  have hinj : Function.Injective (fun M : Matrix (Fin n) (Fin n) O => M.map O.subtype) :=
    Matrix.map_injective Subtype.val_injective
  have hAB : A * B = 1 := hinj (by
    show (A * B).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
      mul_inv_cancel, Units.val_one])
  have hBA : B * A = 1 := hinj (by
    show (B * A).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
    rw [Matrix.map_mul, hA, hB, Matrix.map_one _ (map_zero _) (map_one _), ← Units.val_mul,
      inv_mul_cancel, Units.val_one])
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  refine Units.ext (Matrix.ext fun i j => ?_)
  rfl

theorem UpperTheory.eventually_map_mem_maximalCompactGL :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (δ : GL (Fin n) E), ∀ᶠ w : Pl E in cofinite,
        GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) δ ∈ GlobalTheory.LFun.KGL w n := by
  intro E _ _ n δ
  have h₁ : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      Valued.v (algebraMap E (w.adicCompletion E) ((δ : Matrix (Fin n) (Fin n) E) i j)) ≤ 1 :=
    eventually_all.2 fun i => eventually_all.2 fun j => val_le_one_ae E _
  have h₂ : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      Valued.v (algebraMap E (w.adicCompletion E)
        (((δ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) i j)) ≤ 1 :=
    eventually_all.2 fun i => eventually_all.2 fun j => val_le_one_ae E _
  filter_upwards [h₁, h₂] with w hw₁ hw₂
  refine mem_GLint (Ov E w) _ (fun i j => ?_) (fun i j => ?_)
  · exact hw₁ i j
  · rw [← map_inv]
    exact hw₂ i j
