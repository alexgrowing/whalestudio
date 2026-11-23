import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.L2Cusps.AbsCompactAlt

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.AutMult GroundTheory.Automorphic

theorem UpperTheory.V.KernelIndexFullLattice.absCompact_holds :
    UpperTheory.V.KernelIndexFullLattice.AbsCompact := by
  intro G G₁ H L _ _ _ _ _ _ _ _ _ _ _ _ _ π ν _ _ ρ W hW J r hr hρ hJ hcpt
  have hmem : ∀ h, J h ∈ W := by
    intro h
    rw [← hJ]
    exact ⟨h, rfl⟩
  let Φ : H →ₗᵢ[ℂ] W :=
    { toLinearMap := (J.toLinearMap).codRestrict W hmem
      norm_map' := fun h => J.norm_map h }
  have hΦsurj : Function.Surjective Φ := by
    intro w
    have hw : (w : L) ∈ J.range := by
      rw [hJ]
      exact w.2
    obtain ⟨h, hh⟩ := hw
    exact ⟨h, Subtype.ext hh⟩
  let Ψ : H ≃ₗᵢ[ℂ] W := LinearIsometryEquiv.ofSurjective Φ hΦsurj
  let Ψc : H →L[ℂ] W := (Ψ.toContinuousLinearEquiv : H →L[ℂ] W)
  let Ψi : W →L[ℂ] H := (Ψ.symm.toContinuousLinearEquiv : W →L[ℂ] H)
  have hΨc : ∀ h, Ψc h = Ψ h := fun h => rfl
  have hΨi : ∀ w, Ψi w = Ψ.symm w := fun w => rfl
  have hrep : ∀ g h, hW.rep g (Ψ h) = Ψ (π (r g) h) := by
    intro g h
    apply Subtype.ext
    exact hρ g h
  intro w hw0
  have hne : Ψ.symm w ≠ 0 := by
    intro h0
    apply hw0
    simpa using congrArg Ψ h0
  obtain ⟨f, hf⟩ := π.exists_integrated_ne_zero ν hne
  refine ⟨Ψc ∘L (π.integrated ν (UnitaryRep.ccToL1 ν f)) ∘L Ψi, ?_, ?_, ?_⟩
  · exact ((hcpt f).comp_clm Ψi).clm_comp Ψc
  · intro S hS x
    rw [mem_homIn_top] at hS
    let T : H →L[ℂ] H := Ψi ∘L S ∘L Ψc
    have hT : T ∈ π.intertwiners π := by
      intro g₁ h
      obtain ⟨g, rfl⟩ := hr g₁
      show Ψ.symm (S (Ψ (π (r g) h))) = π (r g) (Ψ.symm (S (Ψ h)))
      have e1 : S (Ψ h) = Ψ (Ψ.symm (S (Ψ h))) := (Ψ.apply_symm_apply _).symm
      calc Ψ.symm (S (Ψ (π (r g) h))) = Ψ.symm (S (hW.rep g (Ψ h))) := by rw [hrep]
        _ = Ψ.symm (hW.rep g (S (Ψ h))) := by rw [hS]
        _ = Ψ.symm (hW.rep g (Ψ (Ψ.symm (S (Ψ h))))) := by rw [← e1]
        _ = π (r g) (Ψ.symm (S (Ψ h))) := by rw [hrep, LinearIsometryEquiv.symm_apply_apply]
    have hc := UnitaryRep.comp_integrated_of_mem_intertwiners π ν hT (UnitaryRep.ccToL1 ν f)
    have hc' := congrArg (fun Q => Q (Ψ.symm x)) hc
    simp only [T, ContinuousLinearMap.comp_apply, hΨc, hΨi,
      LinearIsometryEquiv.apply_symm_apply] at hc' ⊢
    rw [← hc', LinearIsometryEquiv.apply_symm_apply]
  · simpa [hΨc, hΨi] using hf
