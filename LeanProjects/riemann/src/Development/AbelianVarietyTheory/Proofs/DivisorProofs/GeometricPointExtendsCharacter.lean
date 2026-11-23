import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerGeoHom
open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Cell

theorem exists_geoF_lift : ∀ {P : Type} [CommRing P] (t : PrimeSpectrum P) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : P →+* Ω),
    RingHom.ker χ = t.asIdeal → ∃ em : Cell.GeoF t →+* Ω, em.comp (Cell.geoHom t) = χ := by
  intro P _ t Ω _ _ χ hker
  have h₁ : t.asIdeal ≤ RingHom.ker χ := hker.ge
  have h₂ : t.asIdeal.primeCompl ≤ (IsUnit.submonoid Ω).comap χ := by
    intro x hx
    have hx0 : χ x ≠ 0 := fun h => hx (hker ▸ (RingHom.mem_ker.mpr h))
    exact isUnit_iff_ne_zero.mpr hx0
  haveI hTF : Module.IsTorsionFree t.asIdeal.ResidueField (Cell.GeoF t) := by
    set_option synthInstance.maxHeartbeats 200000 in infer_instance
  let g : t.asIdeal.ResidueField →+* Ω := Ideal.ResidueField.lift t.asIdeal χ h₁ h₂
  letI : Algebra t.asIdeal.ResidueField Ω := g.toAlgebra
  let em : Cell.GeoF t →ₐ[t.asIdeal.ResidueField] Ω := IsAlgClosed.lift (R := t.asIdeal.ResidueField) (S := Cell.GeoF t) (M := Ω)
  refine ⟨em.toRingHom, ?_⟩
  ext r
  simp only [RingHom.comp_apply, Cell.geoHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgHom.commutes]
  exact Ideal.ResidueField.lift_algebraMap t.asIdeal χ h₁ h₂ r

end GlobalTheory.ShFam.Cell
