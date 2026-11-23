import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCAndCoordCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTranslateLiftTorusImageEqAddStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorCorrectedTorusCoordinateRatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCoordinateRatioFibreInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCoordinateRatioEqOneUnitSectionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.MumCmp.TranslCoord

theorem coord_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)), wL.IsGen → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∀ xe : D₂.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U₂.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D₂.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U₂.gt e).t x) r z J') → (∀ χ : D₂.toPre.X, D₂.toPre.c χ ≫ β.hom = D.toPre.c (xe χ)) → ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ (χ : D₂.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.val ((U.gt e).t (xe χ)) (r ≫ h) z J = (∏ k, Geo.Tor.gv w (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) z (fun i => J ((r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ D₂.toPre.Oφ (U₂.gt e).pG χ k)) ^ Oinvε k) * Geo.Tor.val ((U₂.gt e).t χ) r z J' * Geo.Tor.val (g.s (xe χ)) (r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e) z J := by
  intro R _ _ _ hR D A G _ _ hG U g hg a ha hlev A₂ D₂ U₂ wL hwL β hβ hp w hw xe hker hc e h hh hfst χ Z r z J J' hJ hJ'
  have hpg := GlobalTheory.T.uniformisation_translate_lift_torus_image_eq_add R (maximalIdeal R) D D₂ A A₂ G U.toUnifPre U₂.toUnifPre g a β hβ e (hp e)
    (fun ae h1 h2 => (hlev e ae h1 h2).1) h hh hfst
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.exists_generator_corrected_torusCoordinate_ratio (U.gt e) (U₂.gt e) β.hom g w hw χ (xe χ) (hc χ) h hh hpg
  have hp' : (U₂.gt e).pG ≫ β.hom = (U.gt e).pG := Over.OverMorphism.ext (hp e)
  have := (U.gt e).q_flat
  have := (U.gt e).q_surj
  have := (U.gt e).q_affine
  obtain ⟨v, hv, hv'⟩ := GlobalTheory.CoordCompare.exists_gen_of_val_eq D.toPre.P.isLB _ _ (U.gt e).q.left u hu
    (fun Z r r' z J hJ hrr => by
      obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D₂.toPre.P.L D₂.toPre.P.isLB z
      rw [hu' Z r z J J' hJ hJ', hu' Z r' z J J' hJ hJ']
      exact GlobalTheory.T.twistedCoordinateRatio_fibre_invariant (U.gt e) (U₂.gt e) β.hom hp' g w χ (xe χ)
        (fun Z r z J J' hJ hJ' h1 h2 => hker e Z r z J J' hJ hJ' h1 h2 χ) a h hh hfst r r' z J J' hJ hJ' hrr)
  have h1 := GlobalTheory.CoordCompare.val_eq_one GlobalTheory.globalFns_holds (D.toPre.c (xe χ)) _ rfl v hv (fun y J hJ => by
      obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D₂.toPre.P.L D₂.toPre.P.isLB y
      have := (U.gt e).q_hom
      have k := hv' _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶ thickObj R (maximalIdeal R) e G).left y J hJ
      rw [← Over.comp_left, MonObj.one_comp] at k
      rw [k, hu' _ _ y J J' hJ hJ']
      exact GlobalTheory.T.twistedCoordinateRatio_eq_one_unitSection (U.gt e) (U₂.gt e) β.hom g w χ (xe χ) a h hh hfst (fun ae h1 h2 => (hlev e ae h1 h2).2 (xe χ)) y J J' hJ hJ')
    Z (r ≫ (U.gt e).q.left) z J hJ
  rw [hv' Z r z J hJ, hu' Z r z J J' hJ hJ', mul_inv_eq_one] at h1
  exact h1

end GlobalTheory.MumCmp.TranslCoord
