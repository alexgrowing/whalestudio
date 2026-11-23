import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction

noncomputable section

namespace UpperTheory.V.Lit.Dr

theorem shiftZero : ShiftZero := by
  intro Γ M _ _ _ ρ n w hw hlin
  let v : Fin n → (Rep.of ρ).ρ.invariants :=
    fun i => ⟨w i, (Representation.mem_invariants _ _).2 (hw i)⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ∑ i, g i • w i = 0 := by
      have := congrArg Subtype.val hg
      rw [Submodule.coe_sum] at this
      exact this
    rw [hlin g h0]
    intro i
    rfl
  have h1 := hli.cardinal_le_rank
  rw [Cardinal.mk_fin] at h1
  have hinj : Function.Injective (groupCohomology.H0Iso (Rep.of ρ)).inv.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact h1.trans (LinearMap.rank_le_of_injective _ hinj)

end UpperTheory.V.Lit.Dr
