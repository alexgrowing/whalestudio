import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}

def InN (κ : DividedPowers I) {s : X ⟶ Sp R} (T : Thick (dp0 R) s) : Prop :=
  ∃ δ' : DividedPowers (T.J ⊔ I.map (algebraMap R T.B)),
    IsDPMorphism T.δ δ' (RingHom.id T.B) ∧ IsDPMorphism κ δ' (algebraMap R T.B)

def IsChart (s : X ⟶ Sp R) (U : X.affineOpens) : Prop :=
  Module.Flat R (Sec s U.1) ∧
    ∃ (d : ℕ) (t : MvPolynomial (Fin d) R →ₐ[R] Sec s U.1), t.toRingHom.FormallyEtale

abbrev Chart (s : X ⟶ Sp R) : Type := {U : X.affineOpens // IsChart s U}

abbrev bas (s : X ⟶ Sp R) (U : X.affineOpens) : Thick (dp0 R) s :=
  Thick.triv (Sec s U.1) (affPt s U) (affPt_w s U)

structure Tag (γ : DividedPowers I) (s : X ⟶ Sp R) {K : Type} (U : K → X.Opens) : Type 1 where

  T : Thick γ s

  k : K
  le : ⊤ ≤ T.x ⁻¹ᵁ U k

variable {γ : DividedPowers I} {s : X ⟶ Sp R} {K : Type} {U : K → X.Opens}

@[ext] structure Tag.Hom (S T : Tag γ s U) where

  f : S.T ⟶ T.T
  le : U S.k ≤ U T.k

instance : Category (Tag γ s U) where
  Hom := Tag.Hom
  id S := ⟨𝟙 _, le_rfl⟩
  comp f g := ⟨f.f ≫ g.f, f.le.trans g.le⟩
  id_comp _ := Tag.Hom.ext (Category.id_comp _)
  comp_id _ := Tag.Hom.ext (Category.comp_id _)
  assoc _ _ _ := Tag.Hom.ext (Category.assoc _ _ _)

@[ext] theorem Tag.hom_ext {S T : Tag γ s U} {f g : S ⟶ T} (h : f.f = g.f) : f = g := Tag.Hom.ext h

@[simp] theorem Tag.comp_f {S T V : Tag γ s U} (f : S ⟶ T) (g : T ⟶ V) : (f ≫ g).f = f.f ≫ g.f := rfl

@[simp] theorem Tag.id_f (S : Tag γ s U) : Tag.Hom.f (𝟙 S) = 𝟙 S.T := rfl

def Tag.forget (γ : DividedPowers I) (s : X ⟶ Sp R) (U : K → X.Opens) : Tag γ s U ⥤ Thick γ s where
  obj S := S.T
  map f := f.f

end FubiniStudyChowHeightFormula₂.Adr
