import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousConjNilSymm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc GlobalTheory.CompanionTheory.LocVan
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

theorem det_one_add_sqZero {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (M : E →ₗ[ℝ] E) (hM : M * M = 0) : LinearMap.det (1 + M) = 1 := by
  have hnil : IsNilpotent (-M) := ⟨2, by rw [pow_two, neg_mul_neg, hM]⟩
  have hc := hnil.charpoly_eq_X_pow_finrank
  let b := Module.finBasis ℝ E
  have h1 : (LinearMap.toMatrix b b (-M)).charpoly.eval 1 = 1 := by
    rw [LinearMap.charpoly_toMatrix, hc]; simp
  rw [Matrix.eval_charpoly] at h1
  rw [← LinearMap.det_toMatrix b, ← h1]
  congr 1
  simp [map_add, LinearMap.toMatrix_one]

theorem measurePreserving_add_one_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (ν : Measure E)
    [ν.IsAddHaarMeasure] (M : E →ₗ[ℝ] E) (hM : M * M = 0) (Y : E) :
    MeasurePreserving (fun X => Y + (1 + M) X) ν ν := by
  have hdet := det_one_add_sqZero M hM
  have hL : MeasurePreserving (fun X => (1 + M : E →ₗ[ℝ] E) X) ν ν := by
    refine ⟨(LinearMap.continuous_of_finiteDimensional _).measurable, ?_⟩
    have := Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := ν) (f := (1 + M : E →ₗ[ℝ] E))
      (by rw [hdet]; exact one_ne_zero)
    rw [this, hdet]; simp
  exact (measurePreserving_add_left ν Y).comp hL

theorem nmul_measurePreserving : ∀ (n : ℕ) (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) [MeasurableSpace (nilrad W₁ W₂)]
  [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂)) [ν.IsAddHaarMeasure] (Y : nilrad W₁ W₂),
  MeasurePreserving (nmul hW Y) ν ν := by
  intro n W₁ W₂ hW mS bS ν hν Y
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  let M : nilrad W₁ W₂ →ₗ[ℝ] nilrad W₁ W₂ :=
    { toFun := fun X => ⟨Y.1 * X.1, nil_mul_mem hW Y.2 X.2⟩
      map_add' := fun A B => Subtype.ext (by simp [mul_add])
      map_smul' := fun c A => Subtype.ext (by simp) }
  have hM : M * M = 0 := by
    ext1 X
    apply Subtype.ext
    change Y.1 * (Y.1 * X.1) = 0
    have h : ∀ y, (Y.1 * (Y.1 * X.1)) *ᵥ y = 0 := fun y => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact Y.2.2.2 _ (Y.2.2.1 _ (X.2.1 y))
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    simpa using this
  haveI : FiniteDimensional ℝ (nilrad W₁ W₂) := FiniteDimensional.complexToReal _
  have key := @measurePreserving_add_one_add (nilrad W₁ W₂) (Submodule.normedAddCommGroup _)
    (Submodule.normedSpace _) _ mS bS ν hν M hM Y
  convert key using 1
  funext X
  apply Subtype.ext
  change Y.1 + X.1 + Y.1 * X.1 = Y.1 + (X.1 + Y.1 * X.1)
  abel

end GlobalTheory.CompanionTheory.LocVan
