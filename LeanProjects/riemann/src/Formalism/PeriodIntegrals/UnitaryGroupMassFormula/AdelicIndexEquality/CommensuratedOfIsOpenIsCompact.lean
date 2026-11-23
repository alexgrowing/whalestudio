import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Commensurated
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionD

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open Formalism.MainNotions.S

theorem commensurated_of_isOpen_isCompact {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) :
    Commensurated K := by
  intro x
  have hmo : IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    have hset : ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) =
        (fun y => x⁻¹ * y * x) ⁻¹' (K : Set G) := by
      ext y
      simp only [Subgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨k, hk, rfl⟩
        simpa [mul_assoc] using hk
      · intro h
        exact ⟨_, h, by group⟩
    rw [hset]
    exact ho.preimage (by fun_prop)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hc
  have hso : IsOpen (((K.map (MulAut.conj x).toMonoidHom).subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hmo.preimage continuous_subtype_val
  have : Finite (K ⧸ (K.map (MulAut.conj x).toMonoidHom).subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ hso
  exact Subgroup.index_ne_zero_of_finite

theorem ksub_isOpen (I : AutInst) : IsOpen ((PI.AdIndexEq.Ksub I : Subgroup I.Gf) : Set I.Gf) :=
  PI.WAU.kset_open I

theorem ksub_isCompact (I : AutInst) : IsCompact ((PI.AdIndexEq.Ksub I : Subgroup I.Gf) : Set I.Gf) :=
  PI.WAU.maximal_compact_isCompact I

theorem compact_commensurated : KComm := fun I =>
  commensurated_of_isOpen_isCompact _ (ksub_isOpen I) (ksub_isCompact I)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
