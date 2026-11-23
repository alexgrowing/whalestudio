import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DualCountBound.LatticeStabilizerFixed

noncomputable section

open ValuativeRel Topology

namespace PI.NGStepBBW

open Formalism.MainNotions.S.Loc

theorem isOpen_locO {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : LocE F E) : IsOpen (L.O : Set E) := by
  have _ := L.top
  have _ := L.free
  have _ : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  have _ : ContinuousAdd E := IsModuleTopology.toContinuousAdd F E
  have halg : ∀ x : E, IsAlgebraic 𝒪[F] x := fun x =>
    (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  let b := Module.finBasisOfFinrankEq F E L.rank
  have hc : ∀ i, ∃ c : 𝒪[F], c ≠ 0 ∧ IsIntegral 𝒪[F] (c • b i) := fun i =>
    (halg (b i)).exists_integral_multiple
  choose c hc0 hci using hc
  have hcF : ∀ i, ((c i : 𝒪[F]) : F) ≠ 0 := fun i h => hc0 i (Subtype.ext h)
  let b' := b.unitsSMul (fun i => Units.mk0 ((c i : F)) (hcF i))
  have hb'O : ∀ i, b' i ∈ L.O := by
    intro i
    rw [Module.Basis.unitsSMul_apply, L.O_def, Units.smul_def, Units.val_mk0]
    exact hci i
  have hint : ∀ a ∈ 𝒪[F], algebraMap F E a ∈ L.O := fun a ha =>
    (L.O_def _).2 (isIntegral_algebraMap (x := (⟨a, ha⟩ : 𝒪[F])))
  let S : Set E := b'.equivFun ⁻¹' (Set.pi Set.univ fun _ => (𝒪[F] : Set F))
  have hSo : IsOpen S := by
    refine IsOpen.preimage ?_ ?_
    · exact IsModuleTopology.continuous_of_linearMap (b'.equivFun : E →ₗ[F] (Fin 2 → F))
    · exact isOpen_set_pi Set.finite_univ fun i _ =>
        Valuation.isOpen_integer (v := ValuativeRel.valuation F)
  have hSO : S ⊆ L.O := by
    intro x hx
    rw [← b'.sum_equivFun x]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact L.O.mul_mem (hint _ (hx i (Set.mem_univ i))) (hb'O i)
  have h0 : (0 : E) ∈ S := by
    intro i _
    simp only [map_zero, Pi.zero_apply]
    exact zero_mem _
  have hnhds : ((L.O.toAddSubgroup : AddSubgroup E) : Set E) ∈ 𝓝 (0 : E) :=
    Filter.mem_of_superset (hSo.mem_nhds h0) hSO
  exact AddSubgroup.isOpen_of_mem_nhds L.O.toAddSubgroup hnhds

end PI.NGStepBBW
