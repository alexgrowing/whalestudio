import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitUniformisationMumfordBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtensionDvrFractionFieldsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmetricBundleDescendsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericUniformisedPullbackMumfordBundleMatchingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportPolarisedVarietyFiniteExtensionFractionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationCompleteTraitBaseChangeFiniteExtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationBundleGenericFibreDescentStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_finExt_trait_unif_lam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂), FinExt ρ ∧ ∀ (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (β : G₂.left ⟶ G.left) (β₂ : (G2 G₂).left ⟶ (G2 G).left), IsGrpPullback G₂ G (spMap ρ) β → Geo.Tor.IsSquare β β₂ → ∃ (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) (PP.pull β₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP
  obtain ⟨W, _, _, _, φ, GW, _, _, βW, βW₂, DW, AW, UW, hW, hφi, hφl, hpbW, hsqW, hlamW⟩ :=
    GlobalTheory.T.exists_trait_uniformisation_mumfordBundle R hR G hG A gen hgen PP hPP
  obtain ⟨ga, α, α₂, hga, hpbα, hsqα, hlamα, hcompα⟩ :=
    GlobalTheory.T.generic_uniformised_pullback_mumfordBundle_matching R hR G hG A gen hgen PP hPP W φ GW βW βW₂ DW AW UW hW hφi hφl hpbW hsqW hlamW

  have : CharZero R := hR.2
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨K', _, io, Ω', _, j, l, A₁, α₁, α₁₂, p, hio, hlio, hpb₁, hsq₁, hlam₁, hp₁, hp₂, hpL⟩ :=
    GlobalTheory.T.exists_finite_extension_symmetric_bundle_descends (FractionRing R) (FractionRing W) ga A AW α α₂ hpbα hsqα hlamα
  have hcomp : ∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r)) := by
    intro r
    have h := DFunLike.congr_fun hlio (algebraMap R (FractionRing R) r)
    simp only [RingHom.comp_apply] at h
    rw [h, hga]
  obtain ⟨R₂, _, _, _, ρ, i, W₂, _, _, _, σ, φ₂, j₂, hρ, hW₂, hσ, hσl, hφ₂i, hφ₂l, hsq, hi, hj₂, hl₂⟩ :=
    GlobalTheory.T.exists_common_extension_dvr_fraction_fields R W hR hW φ hφi hφl K' Ω' io j l hio hcomp
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ, hρ, ?_⟩
  intro G₂ _ _ β β₂ hpb₂ hsq₂
  obtain ⟨A₂, gen₂, q, hgen₂, hext₂, hpbq, hlamq, hcompq⟩ :=
    GlobalTheory.T.transport_polarisedVariety_finiteExtension_fraction R G A gen hgen PP hPP K' io A₁ α₁ α₁₂ hpb₁ hsq₁ hlam₁ R₂ ρ i hρ.2.1 hi G₂ β β₂ hpb₂ hsq₂
  obtain ⟨GW', _, _, βW', τ, DW', AW', UW', κ, hpbW', hpbτ, hβτ, hκ, hLτ⟩ :=
    GlobalTheory.T.uniformisation_completeTrait_baseChange_finite_ext R R₂ W W₂ ρ φ σ φ₂ hR hW hW₂ hσ hσl hsq hφ₂i G hG G₂ β hpb₂ GW βW hpbW DW AW UW
  refine ⟨A₂, gen₂, W₂, inferInstance, inferInstance, inferInstance, φ₂, GW', inferInstance, inferInstance,
    βW', DW', AW', UW', κ, hgen₂, hext₂, hW₂, hφ₂i, hφ₂l, hpbW', hκ, ?_⟩
  exact GlobalTheory.T.uniformisation_bundle_genericFibre_descent R W R₂ W₂ K' Ω' φ ρ σ φ₂ io j l i j₂ hφi hρ.2.1 hσ.2.1 hφ₂i hsq hcomp hi hj₂ hl₂
    G A gen GW βW DW AW UW α hpbW hcompα A₁ α₁ p hpb₁ hp₁ hp₂ hpL G₂ β A₂ gen₂ q hpb₂ hpbq hlamq hcompq
    GW' βW' τ DW' AW' UW' κ hpbW' hpbτ hβτ hκ hLτ
