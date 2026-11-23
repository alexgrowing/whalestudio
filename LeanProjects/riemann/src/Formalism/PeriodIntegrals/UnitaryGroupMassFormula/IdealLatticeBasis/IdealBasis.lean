import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdealLatticeBasis.IdealBasisAlt

open NumberField

namespace PI.IdealLatticeWork

theorem idealBasis : IdealBasis := by
  intro K _ _ b cc hcc
  classical
  let bI := Ideal.selfBasis b cc hcc
  refine ⟨(bI 0 : 𝓞 K), (bI 0).2, (bI 1 : 𝓞 K), (bI 1).2, ?_, ?_⟩
  · intro c hc
    refine ⟨bI.repr ⟨c, hc⟩ 0, bI.repr ⟨c, hc⟩ 1, ?_⟩
    have h := congrArg Subtype.val (bI.sum_repr ⟨c, hc⟩)
    rw [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul_of_tower,
      Submodule.coe_smul_of_tower] at h
    exact h.symm
  · refine ⟨b.repr (bI 0) 0, b.repr (bI 0) 1, b.repr (bI 1) 0, b.repr (bI 1) 1, ?_, ?_, ?_⟩
    · have h := b.sum_repr (bI 0 : 𝓞 K)
      rw [Fin.sum_univ_two] at h
      exact h.symm
    · have h := b.sum_repr (bI 1 : 𝓞 K)
      rw [Fin.sum_univ_two] at h
      exact h.symm
    · have h := Ideal.natAbs_det_basis_change b cc bI
      rw [Module.Basis.det_apply, Matrix.det_fin_two] at h
      simp only [Module.Basis.toMatrix_apply, Function.comp_apply] at h
      rw [← h]
      congr 1
      ring

end PI.IdealLatticeWork
