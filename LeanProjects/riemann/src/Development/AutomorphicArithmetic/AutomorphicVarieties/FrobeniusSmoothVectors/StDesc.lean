import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusSplitPrimeDatum
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Pr UpperTheory.V.Fr UpperTheory.V

private theorem sd_locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

theorem UpperTheory.V.Fr.st_desc :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (S : Set (HeightOneSpectrum (𝓞 ℚ))) (C : Type) [Group C] (κ : G ℚ Ω →* C), IsOpen (κ.ker : Set (G ℚ Ω)) → (∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → Ine (F := ℚ) A ≤ κ.ker) → ∃ κS : GS Ω S →* C, κS.comp (toGS Ω S) = κ ∧ IsLocallyConstant κS := by
  intro Ω _ _ _ S C _ κ ho hI
  have hN : NS Ω S ≤ κ.ker := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
      (Subgroup.isClosed_of_isOpen _ ho)
    intro s hs
    simp only [Set.mem_iUnion] at hs
    obtain ⟨v, hv, A, hA, hs⟩ := hs
    exact hI v hv A hA hs
  refine ⟨QuotientGroup.lift (NS Ω S) κ hN, MonoidHom.ext fun _ => rfl, fun T => ?_⟩
  rw [← (QuotientGroup.isQuotientMap_mk (NS Ω S)).isOpen_preimage]
  exact sd_locConst κ ho T
