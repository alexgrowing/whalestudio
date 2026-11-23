import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd3AltAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphyUnramifiedCoefficients
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsAutI
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutCsdIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VWitApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IsModular
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelZeroEqMaximalCompactAlt

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open private tw_iso conj_left matIrr_conj att_iso dg corner_conj from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GdMain
open UpperTheory.GalN.V hiding autCsd_iso
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V
theorem UpperTheory.GalN.V.modOfEnd'_alt {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
    {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ) {g₁ : G ℚ Ω}
    {B : ValuationSubring Ω} {ι : Qbar l ≃+* ℂ} (h : _root_.UpperTheory.V.Z.Win.Dn.AutEnd2A c D.η D.Ψ D.cc g₁ B e ι)
    (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] (r : G ℚ Ω →* GG 3 A)
    (h1 : OrdPt l D.η D.Ψ D.cc g₁ B r) (h2 : TypeII D.η (UnitaryThreeInertia.push A.val r)) (h3 : ∀ g ∈ D.η.ker, (r g).mat 1 1 = 1)
    (W' : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) (h4 : ∀ g ∈ D.η.ker, (W' g).val = corner (UnitaryThreeInertia.push A.val r g).mat)
    (h5 : (W' D.cc).val.trace = 0) (W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l)) (hi : Af.RepIso W' W) : _root_.UpperTheory.V.Z.Win.Dn.IsModularA D ι W := by
  obtain ⟨⟨f, hf⟩, hw⟩ := h A r h1 h2 h3 W' h4 h5
  exact ⟨⟨f, att_iso (tw_iso _ hi) hf⟩, hw.weak_admissible_iso hi⟩
theorem UpperTheory.V.Pr.automorphyUnramified_of_locPrints_kisin_gdEnd :
    Loc.LocalPublishedTheorems → _root_.UpperTheory.V.Pr.GdEndAlt → _root_.UpperTheory.V.Aut.AutomorphyUnramifiedCoefficientsAlt := by
  intro hL H Ω _ _ _ K _ _ _ _ l _ c N _ e ψ D _ ι
  obtain ⟨B, hB, -, -, -, hmem, -⟩ := dat_loc D
  obtain ⟨g₁, hM, hfin, h3, h2⟩ := H Ω K l c N e ψ D ι B hB
  have hA : FinA D g₁ := finA_of_end hL D g₁ hM B hmem hfin
  refine ⟨g₁, hM, hA, fun U S ξ r hr hp hI => ?_, fun U S ξ r hp hII h11 W hW => ?_⟩
  · obtain ⟨A, _, _, t, r', ho, ht⟩ := exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp
    have hl : ∀ s ∈ D.η.ker, (UnitaryThreeInertia.push A.val r' s).left = tor _ t * (r s).left * (tor _ t)⁻¹ := fun s hs => by
      rw [ht, conj_left r _ _ ((hr s).trans hs)]
    have hI' : TypeI D.η (UnitaryThreeInertia.push A.val r') := matIrr_conj (tor _ t) (fun s hs => by
      rw [mats, mats, GG.mat, GG.mat, hl s hs, ← Units.val_mul, ← Units.val_mul]
      congr 1
      group) hI
    have hm : HasMult D.η (UnitaryThreeInertia.push A.val r') := ho.red.mult
    have hiso : Af.RepIso (D.rhoK r hr) (D.rhoK _ hm) :=
      ⟨tor _ t, fun s => hl _ (D.η_ker.ge (Base.galEmb_mem ℚ K Ω s))⟩
    have key := h3 A r' ho (matIrr_open_gd D g₁ hM B hB A r' ho hI') (D.rhoK _ hm) fun s => rfl
    exact _root_.UpperTheory.GalN.V.autCsd_iso_alt (tw_iso _ hiso.symm') key
  · obtain ⟨A, _, _, t, r', ho, ht⟩ := exists_ordPt_of_point hL D g₁ hM U S hA B hmem ξ r hp
    let W' : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l) := (MulAut.conj (dg t)).toMonoidHom.comp W
    have hW' : ∀ s, W' s = dg t * W s * (dg t)⁻¹ := fun s => rfl
    have hII' : TypeII D.η (UnitaryThreeInertia.push A.val r') := by
      rw [ht]
      refine ⟨fun g hg a b hab => ?_, matIrr_conj (dg t) (fun s _ => ?_) hII.2⟩
      · rw [(conjBy_tor r t).1, hII.1 g hg a b hab, mul_zero]
      · rw [corner_conj]
        simp only [← Matrix.mul_assoc]
        rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    exact _root_.UpperTheory.GalN.V.modOfEnd'_alt D h2 A r' ho hII' (fun g hg => by
      apply Subtype.ext
      show (UnitaryThreeInertia.push A.val r' g).mat 1 1 = 1
      rw [ht, (conjBy_tor r t).1, h11 g hg]
      simp [wt]) W' (fun g hg => by
      rw [ht, corner_conj, hW', Units.val_mul, Units.val_mul, hW.1 g hg]) (by
      rw [hW', Units.val_mul, Units.val_mul, Matrix.trace_units_conj, hW.2]) W (Af.RepIso.symm' ⟨dg t, hW'⟩)
end
