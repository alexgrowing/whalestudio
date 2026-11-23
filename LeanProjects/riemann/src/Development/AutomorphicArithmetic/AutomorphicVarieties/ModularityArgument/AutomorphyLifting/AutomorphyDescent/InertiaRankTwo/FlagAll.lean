import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.DownCsdK

open UpperTheory.V.Z.Win.Dn
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.BasicNotions UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win
open scoped Pointwise

theorem UpperTheory.V.Z.Win.Dn.flagAll_of :
    FlagAll := by
  intro F Ω _ _ _ _ _ l _ n r h v hv B hB
  obtain ⟨A, hA, κ, P, hP⟩ := h v hv
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA hB
  have hmem : ∀ s ∈ Dec (F := F) (g • A), g⁻¹ * s * g ∈ Dec (F := F) A := fun s hs => by
    have h1 : s • g • A = g • A := hs
    show (g⁻¹ * s * g) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  let d : ↥(Dec (F := F) (g • A)) →* ↥(Dec (F := F) A) :=
    { toFun := fun s => ⟨g⁻¹ * s * g, hmem s s.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp [mul_assoc] }
  refine ⟨fun i => (κ i).comp d, P * r g⁻¹, fun s => ?_⟩
  have e : P * r g⁻¹ * r s * (P * r g⁻¹)⁻¹ = P * r (d s) * P⁻¹ := by
    show _ = P * r (g⁻¹ * s * g) * P⁻¹
    rw [map_mul, map_mul, map_inv]
    group
  rw [e]
  exact hP (d s)
