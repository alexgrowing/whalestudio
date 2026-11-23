import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

def IsTan {Z Y : Scheme.{0}} {s : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} (d : ℕ) (c1 c2 : Y ⟶ Z) (h1 : c1 ≫ s = s') (h2 : c2 ≫ s = s')
    (y : CxPts s' (RingHom.id ℂ)) (A : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (U : Z.Opens) (V : Y.Opens) (hV1 : V ≤ c1 ⁻¹ᵁ U) (hV2 : V ≤ c2 ⁻¹ᵁ U) (t : Fin d → Sec s U),
    y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V ∧ IsAffineOpen U ∧ IsAffineOpen V ∧
    ∃ φ : Ω[Sec s' V⁄ℂ] →ₗ[ℂ] (Fin d → ℂ),
      (∀ (b : Sec s' V) (ω : Ω[Sec s' V⁄ℂ]), φ (b • ω) = CxPts.ev s' (RingHom.id ℂ) V b y • φ ω) ∧
      (∀ l, φ (D ℂ (Sec s' V) (Sec.res s' hV1 (appSec s s' c1 U (t l)))) = Pi.single l 1) ∧
      (∀ j, φ (D ℂ (Sec s' V) (Sec.res s' hV2 (appSec s s' c2 U (t j)))) = fun l => A j l) ∧
      ∀ ω : Ω[Sec s' V⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → Sec s' V) (ω' : Fin m → Ω[Sec s' V⁄ℂ]),
        (∀ i, CxPts.ev s' (RingHom.id ℂ) V (b i) y = 0) ∧ ω = ∑ i, b i • ω' i

def IsGal {Z W : Scheme.{0}} {s : Z ⟶ Sp ℂ} {sW : W ⟶ Sp ℂ} (π : W ⟶ Z) (hπ : π ≫ s = sW) (G : Type) [Group G]
    (act : G → (W ⟶ W)) : Prop :=
  GlobalTheory.ZM.IsGaloisCover G (fun g => act g⁻¹) π

namespace IsGal

variable {Z W : Scheme.{0}} {s : Z ⟶ Sp ℂ} {sW : W ⟶ Sp ℂ} {π : W ⟶ Z} {hπ : π ≫ s = sW} {G : Type} [Group G]
  {act : G → (W ⟶ W)}

theorem mk' (hG : Finite G) (hfin : IsFinite π) (het : Etale π) (hon : Surjective π) (hinv : ∀ g, act g ≫ π = π)
    (hmul : ∀ g h, act (g * h) = act h ≫ act g) (hone : act 1 = 𝟙 W)
    (hfib : ∀ (K : Type) [Field K] [IsAlgClosed K] (a b : Sp K ⟶ W), a ≫ π = b ≫ π → ∃! g : G, b = a ≫ act g) :
    IsGal π hπ G act where
  finite := hG
  one := by simp [hone]
  mul a c := by simp only [mul_inv_rev]; exact hmul c⁻¹ a⁻¹
  inv a := hinv a⁻¹
  fin := hfin
  etale := het
  onto := hon
  fibre K _ _ y y' e := by
    obtain ⟨g, hg, hu⟩ := hfib K y y' e
    refine ⟨g⁻¹, by simp [hg], fun a ha => ?_⟩
    have := hu a⁻¹ (by simpa using ha.symm)
    simp [← this]

theorem finite (h : IsGal π hπ G act) : Finite G := GlobalTheory.ZM.IsGaloisCover.finite h
theorem isFinite (h : IsGal π hπ G act) : IsFinite π := GlobalTheory.ZM.IsGaloisCover.fin h
theorem etale (h : IsGal π hπ G act) : Etale π := GlobalTheory.ZM.IsGaloisCover.etale h
theorem surjective (h : IsGal π hπ G act) : Surjective π := GlobalTheory.ZM.IsGaloisCover.onto h

theorem act_comp (h : IsGal π hπ G act) (g : G) : act g ≫ π = π := by
  simpa using GlobalTheory.ZM.IsGaloisCover.inv h g⁻¹

theorem act_mul (h : IsGal π hπ G act) (g g' : G) : act (g * g') = act g' ≫ act g := by
  simpa using GlobalTheory.ZM.IsGaloisCover.mul h g'⁻¹ g⁻¹

theorem act_one (h : IsGal π hπ G act) : act 1 = 𝟙 W := by
  simpa using GlobalTheory.ZM.IsGaloisCover.one h

theorem fibre (h : IsGal π hπ G act) (K : Type) [Field K] [IsAlgClosed K] (a b : Sp K ⟶ W) :
    a ≫ π = b ≫ π ↔ ∃! g : G, b = a ≫ act g := by
  constructor
  · intro e
    obtain ⟨g, hg, hu⟩ := GlobalTheory.ZM.IsGaloisCover.fibre h K a b e
    refine ⟨g⁻¹, hg.symm, fun g' hg' => ?_⟩
    have := hu g'⁻¹ (by simpa using hg'.symm)
    simp [← this]
  · rintro ⟨g, hg, -⟩
    rw [hg, Category.assoc, h.act_comp]

theorem fibre_cx (h : IsGal π hπ G act) (a b : CxPts sW (RingHom.id ℂ)) :
    a.1 ≫ π = b.1 ≫ π ↔ ∃! g : G, b.1 = a.1 ≫ act g :=
  h.fibre ℂ a.1 b.1

end IsGal

example : IsGal (Z := Sp ℂ) (W := Sp ℂ) (s := 𝟙 _) (sW := 𝟙 _) (𝟙 _) (by simp) Unit (fun _ => 𝟙 _) :=
  IsGal.mk' inferInstance inferInstance inferInstance inferInstance (fun _ => by simp) (fun _ _ => by simp) rfl
    (fun _ _ _ a b e => ⟨(), by simpa using e.symm, fun _ _ => rfl⟩)

example (G : Type) [Group G] : ¬ IsGal (Z := Sp ℂ) (W := (∅ : Scheme.{0})) (s := 𝟙 _) (sW := Scheme.emptyTo _)
    (Scheme.emptyTo _) (by simp) G (fun _ => 𝟙 _) := by
  intro h
  have := h.surjective
  obtain ⟨x, -⟩ := (Scheme.emptyTo (Sp ℂ)).surjective (IsLocalRing.closedPoint ℂ)
  exact isEmptyElim x

example : ¬ IsGal (Z := Sp ℂ) (W := Sp ℂ) (s := 𝟙 _) (sW := 𝟙 _) (𝟙 _) (by simp) ℤˣ (fun _ => 𝟙 _) := by
  intro h
  obtain ⟨g, -, hu⟩ := (h.fibre ℂ (𝟙 _) (𝟙 _)).1 rfl
  have := (hu 1 (by simp)).trans (hu (-1) (by simp)).symm
  exact absurd this (by decide)

end GlobalTheory.W1
