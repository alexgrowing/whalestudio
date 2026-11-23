import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in
theorem UpperTheory.V.Loc.laCyc :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → IsWtPart h ((cycBar F Ω l).comp (Dec (F := F) A).subtype) (fun _ => -1) 1 := by
  intro H F Ω _ _ _ _ _ l _ A w h _
  refine ⟨by simp, fun a ha σ => ?_⟩
  obtain ⟨art, hart⟩ := H F Ω
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι (CharAboveModel.absPow_isAlgPos F 1)
  have e : μ = cycBar F Ω l ^ 1 := CharAboveModel.eq_cyc_pow hart hμ hL
  rw [pow_one] at e
  subst e
  have h1 := hL.loc (a (ineIncl h σ)) _ (ha.glob art hart (ineIncl h σ))
  have hu : Formalism.L2.Host.IsUnitAt w (a (ineIncl h σ)) := by
    have h2 := ha.ord_eq (ineIncl h σ)
    rw [deg_ineIncl, neg_zero] at h2
    haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F))
      (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ)))).eq_one_iff_eq_one.1
      (GlobalTheory.SmGL.ord_eq_zero_iff.1 h2)
  rw [(Model.absPow_isAbsPow F (1 : ℕ)).1 w _ hu] at h1
  simp only [Units.val_one, map_one, one_mul, locPow] at h1
  simpa using h1
