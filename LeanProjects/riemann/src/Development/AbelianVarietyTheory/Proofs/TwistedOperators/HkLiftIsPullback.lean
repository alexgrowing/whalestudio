import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivHeckeKernelSchemePointsHeckeKernels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRigIsoOfIsGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTransferPts
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsPointedOfIsHkIsog
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

section Map

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] (h : Sp T ⟶ Z.Hk)

def hkLift {x : Sp T ⟶ Xo.X} (hx : x = h ≫ Z.π₁) : Gx x ⟶ Z.o₁.t.G.left :=
  Z.m₁.cart.1.lift (snd (Over.mk x) Xo.univ.t.G).left ((fst (Over.mk x) Xo.univ.t.G).left ≫ h)
    (by rw [GlobalTheory.HeckeFrCompare.snd_hom, Category.assoc, ← hx])

def hkLift₂ {x' : Sp T ⟶ Xo.X} (hx' : x' = h ≫ Z.π₂) : Gx x' ⟶ Z.o₂.t.G.left :=
  Z.m₂.cart.1.lift (snd (Over.mk x') Xo.univ.t.G).left ((fst (Over.mk x') Xo.univ.t.G).left ≫ h)
    (by rw [GlobalTheory.HeckeFrCompare.snd_hom, Category.assoc, ← hx'])

variable {h} {x x' : Sp T ⟶ Xo.X} (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂)

@[reassoc] theorem hkLift_φ : hkLift Z h hx ≫ Z.m₁.cm.F = (snd (Over.mk x) Xo.univ.t.G).left :=
  Z.m₁.cart.1.lift_fst _ _ _

@[reassoc] theorem hkLift_hom : hkLift Z h hx ≫ Z.o₁.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ h :=
  Z.m₁.cart.1.lift_snd _ _ _

@[reassoc] theorem hkLift₂_φ : hkLift₂ Z h hx' ≫ Z.m₂.cm.F = (snd (Over.mk x') Xo.univ.t.G).left :=
  Z.m₂.cart.1.lift_fst _ _ _

@[reassoc] theorem hkLift₂_hom : hkLift₂ Z h hx' ≫ Z.o₂.t.G.hom = (fst (Over.mk x') Xo.univ.t.G).left ≫ h :=
  Z.m₂.cart.1.lift_snd _ _ _

def hkMap : Gx x ⟶ Gx x' :=
  pullback.lift (f := (Over.mk x').hom) (g := Xo.univ.t.G.hom) (fst (Over.mk x) Xo.univ.t.G).left
    (hkLift Z h hx ≫ Z.ψ.left ≫ Z.m₂.cm.F) (by
      simp only [Category.assoc]
      rw [Z.m₂.cart.1.w, Over.w_assoc Z.ψ, hkLift_hom_assoc, ← hx']; rfl)

@[reassoc] theorem hkMap_fst :
    hkMap Z hx hx' ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left :=
  pullback.lift_fst _ _ _

@[reassoc] theorem hkMap_snd :
    hkMap Z hx hx' ≫ (snd (Over.mk x') Xo.univ.t.G).left = hkLift Z h hx ≫ Z.ψ.left ≫ Z.m₂.cm.F :=
  pullback.lift_snd _ _ _

@[reassoc] theorem hkMap_hkLift₂ : hkMap Z hx hx' ≫ hkLift₂ Z h hx' = hkLift Z h hx ≫ Z.ψ.left :=
  Z.m₂.cart.1.hom_ext (by rw [Category.assoc, hkLift₂_φ, hkMap_snd, Category.assoc])
    (by rw [Category.assoc, hkLift₂_hom, hkMap_fst_assoc, Category.assoc, Over.w Z.ψ, hkLift_hom])

end Map

section Square

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

theorem hkLift_isPullback (hx : x = h ≫ Z.π₁) :
    IsPullback (hkLift Z h hx) (fst (Over.mk x) Xo.univ.t.G).left Z.o₁.t.G.hom h := by
  refine IsPullback.of_right (h₁₂ := Z.m₁.cm.F) (v₁₃ := Xo.univ.t.G.hom) (h₂₂ := Z.π₁) ?_ (hkLift_hom Z hx)
    Z.m₁.cart.1
  rw [hkLift_φ, ← hx]
  exact (IsPullback.of_hasPullback (Over.mk x).hom Xo.univ.t.G.hom).flip

theorem hkLift₂_isPullback (hx' : x' = h ≫ Z.π₂) :
    IsPullback (hkLift₂ Z h hx') (fst (Over.mk x') Xo.univ.t.G).left Z.o₂.t.G.hom h := by
  refine IsPullback.of_right (h₁₂ := Z.m₂.cm.F) (v₁₃ := Xo.univ.t.G.hom) (h₂₂ := Z.π₂) ?_ (hkLift₂_hom Z hx')
    Z.m₂.cart.1
  rw [hkLift₂_φ, ← hx']
  exact (IsPullback.of_hasPullback (Over.mk x').hom Xo.univ.t.G.hom).flip

theorem hkMap_isPullback (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) :
    IsPullback (hkLift Z h hx) (hkMap Z hx hx') Z.ψ.left (hkLift₂ Z h hx') := by
  refine IsPullback.of_bot ?_ (hkMap_hkLift₂ Z hx hx').symm (hkLift₂_isPullback Z hx')
  rw [hkMap_fst, Over.w Z.ψ]
  exact hkLift_isPullback Z hx

theorem hkMap_etale (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : Etale (hkMap Z hx hx') :=
  MorphismProperty.of_isPullback (P := @Etale) (hkMap_isPullback Z hx hx') Z.isog.1.2.2.1

theorem hkMap_surjective (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂) : Surjective (hkMap Z hx hx') :=
  MorphismProperty.of_isPullback (P := @Surjective) (hkMap_isPullback Z hx hx') Z.isog.1.2.2.2.1

end Square

section Fibre

variable (Z : Corr Xo P p i) {T : Type} [CommRing T] {h : Sp T ⟶ Z.Hk} {x x' : Sp T ⟶ Xo.X}

@[reassoc] theorem isCan_hkLift {Ω : Type} [CommRing Ω] {χ : T →+* Ω} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x}
    (hx : x = h ≫ Z.π₁) (hp : IsCan χ pm) (h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁) :
    pm ≫ hkLift Z h hx = hkLift Z (spMap χ ≫ h) h₁ :=
  Z.m₁.cart.1.hom_ext (by rw [Category.assoc, hkLift_φ, hkLift_φ, hp.2.1])
    (by rw [Category.assoc, hkLift_hom, hkLift_hom, reassoc_of% hp.2.2])

theorem isFib_hkMap {Ω : Type} [CommRing Ω] (χ : T →+* Ω) (hx : x = h ≫ Z.π₁) (hx' : x' = h ≫ Z.π₂)
    {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} (hΨ : IsFib χ (hkMap Z hx hx') Ψ₁) :
    ∃ (h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁) (h₂ : x₁' = (spMap χ ≫ h) ≫ Z.π₂), Ψ₁ = hkMap Z h₁ h₂ := by
  obtain ⟨pm, pm', hp, hp', e, f⟩ := hΨ
  have h₁ : x₁ = (spMap χ ≫ h) ≫ Z.π₁ := by rw [hp.1, hx, Category.assoc]
  have h₂ : x₁' = (spMap χ ≫ h) ≫ Z.π₂ := by rw [hp'.1, hx', Category.assoc]
  refine ⟨h₁, h₂, GlobalTheory.HeckeFrCompare.gx_ext (f.trans (hkMap_fst Z h₁ h₂).symm) ?_⟩
  rw [hkMap_snd Z h₁ h₂, ← isCan_hkLift_assoc Z hx hp h₁, ← hkMap_snd Z hx hx', ← reassoc_of% e, hp'.2.1]

end Fibre

end GlobalTheory.HeckeEx
