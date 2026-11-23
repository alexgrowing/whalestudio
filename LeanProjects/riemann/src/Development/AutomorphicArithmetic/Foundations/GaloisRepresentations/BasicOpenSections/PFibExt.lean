import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PChart
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtLift
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFibFin

open CategoryTheory Limits AlgebraicGeometry UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.Mod

private theorem pt_sp {Ω Ω' : Type} [Field Ω] [Field Ω'] (a : Ω →+* Ω') {X : Scheme.{0}} (x : gp Ω ⟶ X) :
    pt (sp a ≫ x) = pt x := by
  rw [pt_comp, pt_eq]

private instance sp_flat {Ω Ω' : Type} [Field Ω] [Field Ω'] (a : Ω →+* Ω') : Flat (sp a) := by
  letI := a.toAlgebra
  exact (inferInstance : Flat (Spec.map (CommRingCat.ofHom (algebraMap Ω Ω'))))

private instance sp_surj {Ω Ω' : Type} [Field Ω] [Field Ω'] (a : Ω →+* Ω') : Surjective (sp a) := by
  refine ⟨fun t => ⟨IsLocalRing.closedPoint Ω', ?_⟩⟩
  exact Subsingleton.elim (α := PrimeSpectrum Ω) _ _

private theorem sp_epi {Ω Ω' : Type} [Field Ω] [Field Ω'] (a : Ω →+* Ω') : Epi (sp a) :=
  Flat.epi_of_flat_of_surjective _

theorem fibExt : FibExt := by
  intro Z Y g _ Ω Ω' _ _ _ a x
  have hepi := sp_epi a
  have inj : ∀ {T : Scheme.{0}} (y y' : gp Ω ⟶ T), sp a ≫ y = sp a ≫ y' → y = y' :=
    fun y y' h => (cancel_epi (sp a)).1 h
  refine ⟨fibFin_of chart_of g Ω x, ⟨?_, ?_, ?_⟩, fun y y' h => inj y y' h⟩
  · intro z hz
    have hz' : z ≫ g = x := hz
    change (sp a ≫ z) ≫ g = sp a ≫ x
    rw [Category.assoc, hz']
  · intro z _ z' _ h
    exact inj z z' h
  · intro w hw
    have hw' : w ≫ g = sp a ≫ x := hw
    let z2 : gp Ω' ⟶ pullback g x := pullback.lift w (sp a) hw'
    obtain ⟨z0, h0, hpt⟩ := ptLift_of (pullback.snd g x) Ω (𝟙 (gp Ω)) (pt z2)
      (Subsingleton.elim (α := PrimeSpectrum Ω) _ _)
    have e : sp a ≫ z0 = z2 := by
      refine ptOne_of chart_of Ω (pullback.snd g x) Ω' (sp a) (sp a ≫ z0) z2 ?_ ?_ ?_
      · rw [Category.assoc, h0, Category.comp_id]
      · exact pullback.lift_snd _ _ _
      · rw [pt_sp, hpt]
    refine ⟨z0 ≫ pullback.fst g x, ?_, ?_⟩
    · change (z0 ≫ pullback.fst g x) ≫ g = x
      rw [Category.assoc, pullback.condition, ← Category.assoc, h0, Category.id_comp]
    · change sp a ≫ z0 ≫ pullback.fst g x = w
      rw [← Category.assoc, e]
      exact pullback.lift_fst _ _ _

end UpperTheory.Gal.Mod
