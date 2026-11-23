import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalArtinLocalIdeleInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharLocalComponentExistsUniqueUnitary
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

theorem UpperTheory.V.Loc.laHecke :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) (art : Neutral.B1.Ideles F →* Gab F Ω), IsGlobalArtin art → ∀ (ι : Qbar l ≃+* ℂ) (χ : Formalism.L2.Host.HChar F) (n : (F →+* ℂ) → ℤ) (μ : G F Ω →* (Qbar l)ˣ), IsLAdicOf art ι χ n μ → (∃ a, IsLocalArtin h a) → IsLocAlg h (μ.comp (Dec (F := F) A).subtype) fun τ => -n ((ι.toRingHom.comp τ.1).comp (algebraMap F (w.adicCompletion F))) := by
  intro F Ω _ _ _ _ _ l _ A w h art hart ι χ n μ hμ ⟨a0, ha0⟩
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' F Ω art hart w
  have hs : GlobalTheory.SmGL.IsSmoothChar (χ.loc w) := GlobalTheory.HeckeComp.smooth_loc χ w
  let φ : Ine (F := F) A →* ℂˣ := ((χ.loc w).comp a0).comp (ineIncl h)
  have hφ : IsOpen (φ.ker : Set (Ine (F := F) A)) := IsOpen.preimage ha0.cont hs
  refine ⟨((Units.map ι.symm.toRingHom.toMonoidHom).comp φ)⁻¹, ?_, fun a ha σ => ?_⟩
  · refine Subgroup.isOpen_mono (fun x hx => ?_) hφ
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [MonoidHom.inv_apply, MonoidHom.comp_apply, hx, map_one, inv_one]
  · have e : a (ineIncl h σ) = a0 (ineIncl h σ) :=
      hinj ((ha.glob art hart _).trans (ha0.glob art hart _).symm)
    have h1 := hμ.loc (a0 (ineIncl h σ)) _ (ha0.glob art hart _)
    have h0 : ι.symm ((χ.loc w (a0 (ineIncl h σ)) : ℂˣ) : ℂ) ≠ 0 := (map_ne_zero ι.symm).2 (Units.ne_zero _)
    rw [e, Units.val_mul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    simp only [neg_neg]
    show ((μ (ineIncl h σ : Weil h) : (Qbar l)ˣ) : Qbar l) * (ι.symm ((χ.loc w (a0 (ineIncl h σ)) : ℂˣ) : ℂ))⁻¹ = locPow ι n w (a0 (ineIncl h σ))
    rw [h1, mul_comm, ← mul_assoc, inv_mul_cancel₀ h0, one_mul]
