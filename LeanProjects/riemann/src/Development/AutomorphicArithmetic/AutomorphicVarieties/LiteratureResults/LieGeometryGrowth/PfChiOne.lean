import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
import GroundTheory.GlobalFields.IdeleGroups.NormOneCompact
open UpperTheory.V.Lit.Geo

open NumberField Formalism.L2.Host GroundTheory.Global in

private theorem norm_of_normOne {E : Type} [Field E] [NumberField E] (χ : HChar E) {y : IdeleGroup E}
    (hy : y ∈ IdeleGroup.normOneSubgroup E) : ‖((χ.1 y : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨D, hD, -, hxD⟩ := IdeleGroup.exists_isCompact_normOneSubgroup E
  have hc : Continuous fun z : IdeleGroup E => ((χ.1 z : ℂˣ) : ℂ) := Units.continuous_val.comp χ.2.1
  obtain ⟨M, hM⟩ := hD.exists_bound_of_continuousOn hc.continuousOn
  have hb : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖((χ.1 z : ℂˣ) : ℂ)‖ ≤ M := fun z hz => by
    obtain ⟨k, hk⟩ := hxD z hz
    have h := hM _ hk
    have h1 : χ.1 (IdeleGroup.diagonal E k) = 1 := χ.2.2 k
    have h2 : χ.1 (IdeleGroup.diagonal E k * z) = χ.1 z :=
      (map_mul χ.1 _ _).trans (by rw [h1, one_mul])
    rwa [h2] at h
  have hle : ∀ z ∈ IdeleGroup.normOneSubgroup E, ‖((χ.1 z : ℂˣ) : ℂ)‖ ≤ 1 := fun z hz => by
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.1 h)
    have h3 := hb _ (pow_mem hz n)
    have h4 : χ.1 (z ^ n) = χ.1 z ^ n := map_pow χ.1 z n
    rw [h4, Units.val_pow_eq_pow_val, norm_pow] at h3
    exact (not_le.2 hn) h3
  have h5 := hle _ (inv_mem hy)
  have h6 : χ.1 y⁻¹ = (χ.1 y)⁻¹ := map_inv χ.1 y
  rw [h6, Units.val_inv_eq_inv_val, norm_inv, inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))] at h5
  exact le_antisymm (hle _ hy) h5

theorem UpperTheory.V.Lit.Geo.Pf.chiOne :
    UpperTheory.V.Lit.Geo.Pf.ChiOne := by
  intro E _ _ _ a χ s _ g
  exact norm_of_normOne χ g.2
