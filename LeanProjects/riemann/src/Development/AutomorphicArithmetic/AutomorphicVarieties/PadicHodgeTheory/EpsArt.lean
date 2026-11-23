import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.L2.Host in
private theorem loc_unr {F : Type} [Field F] [NumberField F] {w : HeightOneSpectrum (𝓞 F)} (χ : HChar F)
    (hu : χ.UnrAt w) (x : (w.adicCompletion F)ˣ) :
    χ.loc w x = χ.val w ^ GlobalTheory.SmGL.ord (w.adicCompletion F) x := by
  have h2 := unif_spec w
  have h0 : Valued.v (x : w.adicCompletion F) ≠ 0 := by simp
  have h1 : IsUnitAt w (x * (atFin w (unif w) ^ GlobalTheory.SmGL.ord (w.adicCompletion F) x)⁻¹) := by
    unfold IsUnitAt IsUnifAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, GlobalTheory.SmGL.SphCompletion.ord_completion]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
    rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
  have h3 := hu _ h1
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
  exact h3

theorem UpperTheory.V.Loc.epsArt :
    GlobalArtinReciprocity → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ s : Weil h, (cycBar F Ω l (s : G F Ω) : Qbar l) = ((normV w : ℕ) : Qbar l) ^ deg s * algPow w (fun _ => 1) (a s : (w.adicCompletion F)) := by
  intro hG F Ω _ _ _ _ _ l _ A w h _ a ha σ
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨art, hart⟩ := hG F Ω
  obtain ⟨μ, hμ, hL⟩ := hart.exists_isLAdicOf ι (GlobalTheory.Published.CharAboveModel.absPow_isAlgPos F 1)
  have e := GlobalTheory.Published.CharAboveModel.eq_cyc_pow hart hμ hL
  have h1 := hL.loc (a σ) σ (ha.glob art hart σ)
  have hu := (Model.absPow_isAbsPow F (1 : ℕ)).1 w
  have hval := (Model.absPow_isAbsPow F (1 : ℕ)).2.1 w
  have h2 : (((Model.absPow F ((1 : ℕ) : ℝ)).loc w (a σ) : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ) ^ deg σ := by
    rw [loc_unr _ hu, ha.ord_eq, Units.val_zpow_eq_zpow_val, hval]
    simp [Complex.cpow_neg, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [h2, e, pow_one, cyc_eq_map_cycZ, map_zpow₀, map_natCast] at h1
  simp only [Nat.cast_one] at h1
  exact h1
