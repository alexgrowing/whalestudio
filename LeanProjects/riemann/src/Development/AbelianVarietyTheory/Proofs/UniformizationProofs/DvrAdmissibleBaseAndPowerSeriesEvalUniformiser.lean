import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsPrincipalIdealRingOfIsLocalization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UniformiserEval

open GlobalTheory.ChartRing

variable {V : Type} [CommRing V] [IsLocalRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V]

omit [IsAdicComplete (IsLocalRing.maximalIdeal V) V] in
theorem C_add_X_mem {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    (PowerSeries.C a + PowerSeries.X : PowerSeries V) ∈ IsLocalRing.maximalIdeal (PowerSeries V) :=
  add_mem (C_mem_maximalIdeal_iff.2 ha) X_mem_maximalIdeal

def translate {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) : PowerSeries V →ₐ[V] PowerSeries V :=
  evalAdic V (IsLocalRing.maximalIdeal (PowerSeries V)) (C_add_X_mem ha)

theorem translate_X {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    translate ha PowerSeries.X = PowerSeries.C a + PowerSeries.X := evalAdic_X _ _

theorem translate_C {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) (x : V) :
    translate ha (PowerSeries.C x) = PowerSeries.C x := (translate ha).commutes x

theorem translate_neg_comp {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    (translate (neg_mem ha)).comp (translate ha) = AlgHom.id V _ := by
  have h : (translate (neg_mem ha)).comp (translate ha) PowerSeries.X = PowerSeries.X := by
    rw [AlgHom.comp_apply, translate_X, map_add, translate_C, translate_X, map_neg]
    ring
  refine algHom_ext_of_isHausdorff (IsLocalRing.maximalIdeal (PowerSeries V)) ?_ h
  rw [h]
  exact X_mem_maximalIdeal

theorem translate_injective {a : V} (ha : a ∈ IsLocalRing.maximalIdeal V) :
    Function.Injective (translate ha) :=
  Function.LeftInverse.injective (g := translate (neg_mem ha)) fun f =>
    DFunLike.congr_fun (translate_neg_comp ha) f

theorem dvr_admissibleBase_and_powerSeries_evalUniformiser : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → IsAdicComplete (IsLocalRing.maximalIdeal V) V → AdmBase V (Ideal.span {ϖ}) ∧ AdmBase (PowerSeries V) (Ideal.span {PowerSeries.X}) ∧ ∃ ev : PowerSeries V →+* V, (∀ x, ev (PowerSeries.C x) = x) ∧ ev PowerSeries.X = ϖ ∧ ∀ (F : Type) [Field F] (i : V →+* F), Function.Injective i → ∃ σ : PowerSeries V →+* PowerSeries F, Function.Injective σ ∧ (∀ x, σ (PowerSeries.C x) = PowerSeries.C (i x)) ∧ σ PowerSeries.X = PowerSeries.C (i ϖ) + PowerSeries.X ∧ ∀ f, PowerSeries.constantCoeff (σ f) = i (ev f) := by
  intro V _ _ _ ϖ hϖ hc
  have hm : ϖ ∈ IsLocalRing.maximalIdeal V := hϖ.not_isUnit
  refine ⟨⟨inferInstance, inferInstance, inferInstance, hϖ.maximalIdeal_eq ▸ hc⟩,
    ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩,
    (PowerSeries.constantCoeff (R := V)).comp (translate hm : PowerSeries V →+* PowerSeries V),
    fun x => ?_, ?_, fun F _ i hi =>
      ⟨(PowerSeries.map i).comp (translate hm : PowerSeries V →+* PowerSeries V), ?_,
        fun x => ?_, ?_, fun f => ?_⟩⟩
  · simp [translate_C]
  · simp [translate_X]
  · exact (PowerSeries.map_injective i hi).comp (translate_injective hm)
  · simp [translate_C]
  · simp [translate_X]
  · simp only [RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map]

end GlobalTheory.UniformiserEval
