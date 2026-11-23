import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulAlt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.Transport
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.GoodTransvection
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianTransvectionSplitting.DiagonalOneJacobian

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.BM

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp PI.UnitaryGroupMassFormula.LocJacTyp
open scoped TensorProduct ENNReal NNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def mulL {ι : Type} (z : ι → Fv F v ⊗[F] E) :
    (ι → Fv F v ⊗[F] E) →ₗ[Fv F v] (ι → Fv F v ⊗[F] E) :=
  LinearMap.pi fun i => (Algebra.lmul (Fv F v) (Fv F v ⊗[F] E) (z i)).comp (LinearMap.proj i)

theorem mulL_apply {ι : Type} (z : ι → Fv F v ⊗[F] E) (c : ι → Fv F v ⊗[F] E) (i : ι) :
    mulL v z c i = z i * c i := rfl

theorem det_mulL {ι : Type} [Fintype ι] [DecidableEq ι] (z : ι → Fv F v ⊗[F] E) :
    haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
    LinearMap.det (mulL v z) = ∏ i, Algebra.norm (Fv F v) (z i) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  unfold mulL
  rw [LinearMap.det_pi]
  simp only [Algebra.norm_apply]

private theorem absV_mul_lemma (x y : Fv F v) : absV v (x * y) = absV v x * absV v y := by
  have hq : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)
  by_cases hx : Valued.v x = 0
  · have hxy : Valued.v (x * y) = 0 := by rw [map_mul, hx, zero_mul]
    simp [absV, hx, hxy]
  by_cases hy : Valued.v y = 0
  · have hxy : Valued.v (x * y) = 0 := by rw [map_mul, hy, mul_zero]
    simp [absV, hy, hxy]
  have hxy : Valued.v (x * y) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hx hy
  unfold absV
  rw [dif_neg hx, dif_neg hy, dif_neg hxy, ← zpow_add₀ hq, ← toAdd_mul]
  congr 2
  rw [← WithZero.coe_inj, WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero,
    WithZero.coe_unzero, map_mul]

private theorem absV_one_lemma_2 : absV v (1 : Fv F v) = 1 := by
  have h1 : Valued.v (1 : Fv F v) ≠ 0 := by
    rw [map_one]
    exact one_ne_zero
  unfold absV
  rw [dif_neg h1]
  have h2 : WithZero.unzero h1 = 1 := by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, map_one, WithZero.coe_one]
  rw [h2, toAdd_one, zpow_zero]

theorem absV_prod {ι : Type} [Fintype ι] (a : ι → Fv F v) :
    absV v (∏ i, a i) = ∏ i, absV v (a i) := by
  let f : Fv F v →* ℝ :=
    { toFun := absV v, map_one' := absV_one_lemma_2 v, map_mul' := absV_mul_lemma v }
  exact map_prod f a Finset.univ

theorem box_measure_mul : BoxMul (E := E) v := by
  classical
  intro ι _ μ _ y hy
  haveI := locallyCompact_Fv v
  haveI := secondCountable_Fv v
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
  haveI : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  let b := Module.finBasis (Fv F v) (Fv F v ⊗[F] E)
  let eR : (Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { b.equivFun with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  haveI : SecondCountableTopology (Fv F v ⊗[F] E) := eR.toHomeomorph.secondCountableTopology
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : BorelSpace (ι → Fv F v ⊗[F] E) := Pi.borelSpace
  let e0 : (ι → Fv F v ⊗[F] E) ≃ₗ[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    (LinearEquiv.piCongrRight fun _ : ι => b.equivFun).trans
      (LinearEquiv.curry (Fv F v) (Fv F v) ι (Fin _)).symm
  let eV : (ι → Fv F v ⊗[F] E) ≃L[Fv F v]
      (ι × Fin (Module.finrank (Fv F v) (Fv F v ⊗[F] E)) → Fv F v) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  let u : ι → (Fv F v ⊗[F] E)ˣ := fun i => (hy i).unit
  let z : ι → Fv F v ⊗[F] E := fun i => ((u i)⁻¹ : (Fv F v ⊗[F] E)ˣ)
  let h : (ι → Fv F v ⊗[F] E) ≃ₜ (ι → Fv F v ⊗[F] E) :=
    { toFun := mulL v y
      invFun := mulL v z
      left_inv := fun c => by
        funext i
        simp only [mulL_apply, z, ← mul_assoc]
        rw [show ((u i)⁻¹ : (Fv F v ⊗[F] E)ˣ).1 * y i = 1 from (u i).inv_mul, one_mul]
      right_inv := fun c => by
        funext i
        simp only [mulL_apply, z, ← mul_assoc]
        rw [show y i * ((u i)⁻¹ : (Fv F v ⊗[F] E)ˣ).1 = 1 from (u i).mul_inv, one_mul]
      continuous_toFun := IsModuleTopology.continuous_of_linearMap (mulL v y)
      continuous_invFun := IsModuleTopology.continuous_of_linearMap (mulL v z) }
  let Em := h.toMeasurableEquiv
  have hNz : ∀ i, Algebra.norm (Fv F v) (z i) * Algebra.norm (Fv F v) (y i) = 1 := fun i => by
    rw [← map_mul, show z i * y i = 1 from (u i).inv_mul, map_one]
  have hdet0 : (∏ i, Algebra.norm (Fv F v) (z i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => left_ne_zero_of_mul_eq_one (hNz i)
  have hLM := PI.NglqJacSplitW.linModulusV_of
    (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)
  set c := PI.NglqJacSplitW.modF (Fv F v) (∏ i, Algebra.norm (Fv F v) (z i)) with hc
  have hmap : μ.map Em = c • μ := by
    ext X hX
    rw [MeasurableEquiv.map_apply, Measure.smul_apply, smul_eq_mul]
    have hpre : Em ⁻¹' X = mulL v z '' X := by
      ext x
      constructor
      · intro hx
        exact ⟨h x, hx, h.left_inv x⟩
      · rintro ⟨w, hw, rfl⟩
        show h (h.symm w) ∈ X
        rw [h.apply_symm_apply]; exact hw
    rw [hpre, hLM (Fv F v) (ι → Fv F v ⊗[F] E) (ι × Fin _) ⟨eV⟩ (mulL v z)
      (by rw [det_mulL]; exact hdet0) μ inferInstance X hX, det_mulL]
  have hS : (Set.univ.pi fun i => {c | y i * c ∈ OEv (E := E) v}) = Em ⁻¹' Obox (E := E) v ι := by
    ext x
    simp [Obox, Em, h, mulL_apply]
  rw [hS, ← MeasurableEquiv.map_apply, hmap, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    hc, modF_Fv v _ hdet0, absV_prod, ENNReal.toReal_ofReal
      (Finset.prod_nonneg fun i _ => (absV_pos v (left_ne_zero_of_mul_eq_one (hNz i))).le),
    mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [eq_inv_of_mul_eq_one_left (hNz i), absV_inv]

end PI.UnitaryGroupMassFormula.LocJacTyp.BM
