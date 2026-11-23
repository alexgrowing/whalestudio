import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp.LevelCmp

theorem lift_comp_pG {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ b.left)
    {A₂ : PolAV (Sp (FractionRing R))} {D₂ : DegData R (maximalIdeal R)} (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (β : D₂.toPre.P.A ≅ D.toPre.P.A) (hβ : ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left)
    (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left) (hh' : h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left) :
    h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom b 0 := by
  classical
  haveI := GlobalTheory.TorsionTranslate.mono_fst (I := maximalIdeal R) e G
  have hs : (thick R (maximalIdeal R) e ≫ a.left) ≫ G.hom = 𝟙 (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, Over.w a]; simp
  let ae : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶ thickObj R (maximalIdeal R) e G :=
    Over.homMk (pullback.lift (thick R (maximalIdeal R) e ≫ a.left) (𝟙 (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left) hs) (pullback.lift_snd _ _ _)
  have hae : ae.left ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left := pullback.lift_fst _ _ _
  have heq : h = (GlobalTheory.MumCmp.Transl.tr ae).left :=
    (cancel_mono (fstG (maximalIdeal R) e G).left).1 (by rw [hh', GlobalTheory.MumCmp.Transl.tr_fst hae])
  have h₁ := GlobalTheory.TorusCoord.im_mul (U.gt e) (toUnit (thickObj R (maximalIdeal R) e G) ≫ ae) (𝟙 (thickObj R (maximalIdeal R) e G))
  have h₂ : GlobalTheory.TorusCoord.im (U.gt e) (toUnit (thickObj R (maximalIdeal R) e G) ≫ ae) = toUnit _ ≫ b := by
    ext
    have := hab e ae.left (Over.w ae) hae
    simp [GlobalTheory.TorusCoord.im] at this ⊢
    rw [this]
  have h₃ : GlobalTheory.TorusCoord.im (U.gt e) (𝟙 (thickObj R (maximalIdeal R) e G)) = (U₂.gt e).pG ≫ β.hom := by
    ext
    have := (hβ e).symm
    simp [GlobalTheory.TorusCoord.im] at this ⊢
    exact this
  have h₅ : GlobalTheory.TorusCoord.im (U.gt e) (GlobalTheory.MumCmp.Transl.tr ae) = (U₂.gt e).pG ≫ (β.hom * (toUnit D₂.toPre.P.A ≫ b)) := by
    rw [GlobalTheory.MumCmp.Transl.tr, h₁, h₂, h₃, comp_mul, comp_toUnit_assoc, mul_comm]
  rw [heq]
  exact congrArg Over.Hom.left h₅

end GlobalTheory.MumCmp.LevelCmp
