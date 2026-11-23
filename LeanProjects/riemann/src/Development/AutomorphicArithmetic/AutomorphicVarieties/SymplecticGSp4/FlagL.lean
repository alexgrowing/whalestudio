import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SplAdjUnit
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.flagL :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ r, D.EPt r → ∃ κ : Fin 4 → D.Gp l →* (PadicAlgCl l)ˣ, Af.IsFlagOn r.toHomUnits (D.Gp l) κ ∧ (∀ i (s : D.Gp l), (s : G ℚ Ω) ∈ D.Ip l → (κ i s : PadicAlgCl l) = ((D.ps i s : c.O) : PadicAlgCl l)) ∧ ∀ i (g : D.Gp l), ‖(κ i g : PadicAlgCl l) - ((D.ps i g : c.O) : PadicAlgCl l)‖ < 1 := by
  intro Ω _ _ _ l _ c D hD r hr
  obtain ⟨R, i1, i2, i3, ρ, y, hpt, rfl⟩ := hr
  obtain ⟨h, κ, hF, h1, h2, -⟩ := UpperTheory.V.Loc.spPtL D hD
    ((mapRep (y : R →+* PadicAlgCl l) ρ.hom).comp (D.Gp l).subtype)
    ⟨R, i1, i2, i3, D.loc ρ l, y, hpt.atL, rfl⟩
  refine ⟨κ, ⟨h⁻¹, fun s => ?_⟩, h1, h2⟩
  rw [inv_inv]
  exact hF s
