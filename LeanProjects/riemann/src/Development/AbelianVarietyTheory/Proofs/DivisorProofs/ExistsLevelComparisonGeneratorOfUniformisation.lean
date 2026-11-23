import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCompPG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalIsoTranslatedBundleLevelComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRatioTranslationTwistIsosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp.LevelCmp

theorem exists_level_gen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)), wL.IsGen → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∃ ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1]), ν.IsGen ∧ ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG (maximalIdeal R) e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G).left) z (N (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e) z J := by
  intro R _ _ _ hR D A G _ _ hG U g hg a ha hab A₂ D₂ U₂ wL hwL β hβm hβ w hw
  have hab' : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left :=
    fun e ae h1 h2 => (hab e ae h1 h2).1
  obtain ⟨W, hW, HW⟩ := GlobalTheory.T.exists_global_iso_translated_bundle_levelComparison hR hG U a ha g.b hab' U₂ wL hwL β hβ
  obtain ⟨ν, hν, Hν⟩ := GlobalTheory.T.exists_generator_ratio_translationTwist_isos D₂.toPre D.toPre β.hom g.b w hw W hW
  refine ⟨ν, hν, ?_⟩
  intro e h hh hh' Z r z J J' N N' hJ hJ' hN hN'
  have k0 := lift_comp_pG U a g.b hab' U₂ β hβ e h hh'
  have hm : r ≫ h ≫ (U.gt e).pG.left = (r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0 := by
    rw [k0, Category.assoc]
  have hf : r ≫ h ≫ (fstG (maximalIdeal R) e G).left = r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
    rw [hh']
  have hs : (r ≫ (U₂.gt e).pG.left) ≫ D₂.toPre.P.A.hom = r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, Over.w]; rfl
  have k2 := Hν Z (r ≫ (U₂.gt e).pG.left) z J (J' (r ≫ (U₂.gt e).pG.left)) hJ (hJ' _)
  have m1 : (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U (J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0)) := by
    have m1' : (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U (J (r ≫ h ≫ (U.gt e).pG.left)) := by
      simpa using hJ (r ≫ h ≫ (U.gt e).pG.left)
    rw [hm] at m1'
    exact m1'
  have m2 : (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U (J' (r ≫ (U₂.gt e).pG.left)) := by
    simpa using hJ' (r ≫ (U₂.gt e).pG.left)
  have m3 : ((toUnit G ≫ a) * 𝟙 G).left ((fstG (maximalIdeal R) e G).left (r z)) ∈ U.LG.L.U (N (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) := by
    simpa using hN (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)
  have m4 : (fstG (maximalIdeal R) e G).left (r z) ∈ U₂.LG.L.U (N' (r ≫ (fstG (maximalIdeal R) e G).left)) := by
    simpa using hN' (r ≫ (fstG (maximalIdeal R) e G).left)
  have k1 := HW e h hh hh' Z r z _ _ _ _ m1 m2 m3 m4
  rw [k2, hs, mul_right_comm, k1, hm, hf]

end GlobalTheory.MumCmp.LevelCmp
