import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteExtensionTopology.Imports

noncomputable section

namespace PI.UnitaryGroupMassFormula.FinExtTop

open PI.FinExtTop

theorem torsionFree_pi_matrix (O' : Type) [CommRing O'] [IsDomain O'] (X' d : Type) [Fintype d]
    [DecidableEq d] : Module.IsTorsionFree O' (X' → Matrix d d (FractionRing O')) where
  isSMulRegular r hr f g h := by
    have hr0 : algebraMap O' (FractionRing O') r ≠ 0 := by
      intro h0
      exact hr.ne_zero ((IsFractionRing.injective O' (FractionRing O')).eq_iff.1
        (h0.trans (map_zero _).symm))
    have h' : algebraMap O' (FractionRing O') r • f = algebraMap O' (FractionRing O') r • g := by
      simpa only [algebraMap_smul] using h
    exact ((IsUnit.mk0 _ hr0).smul_left_cancel).1 h'

theorem expCongruenceExtendsToSum : S4 := by
  intro O' _ _ _ _ _ _ X' d _ _ R' hfin
  let _ : TopologicalSpace R' := moduleTopology O' R'
  have _ : IsModuleTopology O' R' := ⟨rfl⟩
  have _ : IsTopologicalRing R' := IsModuleTopology.isTopologicalRing O' R'
  have _ : ContinuousSMul O' R' := IsModuleTopology.toContinuousSMul O' R'
  have _ := torsionFree_pi_matrix O' X' d
  have _ : Module.IsTorsionFree O' R' := inferInstance
  have _ : Module.Free O' R' := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis O' R'
  have hc : Continuous b.equivFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have _ : T2Space R' := T2Space.of_injective_continuous b.equivFun.injective hc
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨hfin, inferInstance, inferInstance⟩⟩

end PI.UnitaryGroupMassFormula.FinExtTop
