import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedExpansionCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionPullbackTwoTorsionTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTranslateLiftTorusImageEqAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelComparisonGeneratorOfUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusCoordinateUniformisationTranslateEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransportTranslationTwistStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.MumCmp.translate_expansion_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ (σ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), (∀ e : ℕ, U.ExpandsAt e 1 σ f) → ∃ (σ₂ : H0 U₂.LG.L 1) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB 1 α) (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1])), ν.IsGen ∧ (∀ e : ℕ, U₂.ExpandsAt e 1 σ₂ f₂) ∧ ((∀ j, σ₂.f j = 0) → ∀ j, σ.f j = 0) ∧ ∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ D₂.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.sval (f (xe χ)) (r ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0) z J * (Geo.Tor.val (g.s (xe χ)) (r ≫ (toUnit D₂.toPre.P.A).left) z J * Geo.Tor.val ν (r ≫ (toUnit D₂.toPre.P.A).left) z J).val = (∏ κ, Geo.Tor.gv w (r ≫ D₂.toPre.famφB χ κ) z (fun i => J ((r ≫ D₂.toPre.famφB χ κ) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.famφB χ κ)) ^ DegPre.famε 1 κ).val * Geo.Tor.sval (f₂ χ) r z J' := by
  intro R _ _ _ hB D A G _ _ hsa U g hz a ha hlev A₂ D₂ U₂ hL β hβm hβq xe hxe hc w hw σ f hE
  obtain ⟨wL, hwL⟩ := hL
  obtain ⟨ν, hν, hW⟩ := GlobalTheory.T.exists_levelComparison_generator_of_uniformisation R hB D A G hsa U g hz a ha hlev A₂ D₂ U₂ wL hwL β hβm hβq w hw
  obtain ⟨σ₂, hσ₂, h0⟩ := GlobalTheory.T.exists_section_pullback_twoTorsion_translation R G U.LG.L U₂.LG.L U.LG.isLB U₂.LG.isLB a ha wL hwL σ
  obtain ⟨f₂, hf₂⟩ := GlobalTheory.T.exists_translated_expansion_coefficients R D.toPre D₂.toPre β.hom hβm g xe hc w hw ν hν f
  refine ⟨σ₂, f₂, ν, hν, fun e => ?_, h0, hf₂⟩
  obtain ⟨h, hh₁, hh₂⟩ : ∃ h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left,
      h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom ∧
      h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left :=
    ⟨pullback.lift ((fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left) (thickObj R (maximalIdeal R) e G).hom
      (by rw [Category.assoc, Over.w ((toUnit G ≫ a) * 𝟙 G)]; exact pullback.condition),
      pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩
  exact GlobalTheory.T.expansion_transport_translation_twist R (maximalIdeal R) D D₂ A A₂ G U.toUnifPre U₂.toUnifPre a g β.hom xe w wL ν e h hh₂
    (GlobalTheory.T.uniformisation_translate_lift_torus_image_eq_add R (maximalIdeal R) D D₂ A A₂ G U.toUnifPre U₂.toUnifPre g a β hβm e (hβq e)
      (fun ae h1 h2 => (hlev e ae h1 h2).1) h hh₁ hh₂)
    (hW e h hh₁ hh₂) (GlobalTheory.T.torusCoordinate_uniformisation_translate_eq R hB D A G hsa U g hz a ha hlev A₂ D₂ U₂ wL hwL β hβm hβq w hw xe hxe hc e h hh₁ hh₂)
    σ σ₂ f f₂ hσ₂ hf₂ (hE e)
