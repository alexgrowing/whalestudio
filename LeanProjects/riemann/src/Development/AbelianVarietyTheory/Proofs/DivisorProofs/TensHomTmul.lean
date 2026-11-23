import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj Opposite
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs

namespace GlobalTheory.Obs.BC

variable {R₀ R₁ : Type} [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]

theorem isAffine_aff {X : Scheme.{0}} (U : X.affineOpens) : IsAffineOpen U.1 := U.2

def preAff {X₀ X₁ : Scheme.{0}} (pr : X₁ ⟶ X₀) [IsAffineHom pr] : AffOp X₀ ⥤ AffOp X₁ where
  obj U := op ⟨pr ⁻¹ᵁ U.unop.1, (isAffine_aff U.unop).preimage pr⟩
  map a := (homOfLE (pr.preimage_mono (leOfHom a.unop))).op

def natCoef {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F F' : C ⥤ CommAlgCat.{0} R}
    (α : ∀ T, F.obj T →+* F'.obj T) (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) : CoefMap (RingHom.id R) F F' where
  G := 𝟭 C
  α := α
  naturality := nat
  smul := smul

variable {X₀ X₁ : Scheme.{0}} {s₀ : X₀ ⟶ Sp R₀} {s₁ : X₁ ⟶ Sp R₁} {pr : X₁ ⟶ X₀}

def prSec (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)) :
    Sec s₀ U.1 →+* Sec s₁ (pr ⁻¹ᵁ U.1) :=
  GlobalTheory.CechDR.secPull (φ := pr) s₀ s₁ ⟨(⟨pr ⁻¹ᵁ U.1, hU⟩, U), le_rfl⟩

def tensHom (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (U : X₀.affineOpens) (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)) :
    R₁ ⊗[R₀] Sec s₀ U.1 →ₐ[R₁] Sec s₁ (pr ⁻¹ᵁ U.1) :=
  letI : Algebra R₀ (Sec s₁ (pr ⁻¹ᵁ U.1)) := ((algebraMap R₁ _).comp (algebraMap R₀ R₁)).toAlgebra
  haveI : IsScalarTower R₀ R₁ (Sec s₁ (pr ⁻¹ᵁ U.1)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  Algebra.TensorProduct.lift (Algebra.ofId R₁ _)
    { prSec w U hU with commutes' := fun r ↦ (semiHom_secPull w (⟨(⟨pr ⁻¹ᵁ U.1, hU⟩, U), le_rfl⟩ : Pair pr)).map_algebraMap r }
    (fun _ _ ↦ Commute.all _ _)

theorem tensHom_tmul (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) (U : X₀.affineOpens)
    (hU : IsAffineOpen (pr ⁻¹ᵁ U.1)) (r : R₁) (b : Sec s₀ U.1) :
    tensHom w U hU (r ⊗ₜ b) = algebraMap R₁ _ r * prSec w U hU b := by
  simp [tensHom, Algebra.ofId_apply]; rfl

variable [IsAffineHom pr]

theorem prSec_res (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) {U V : AffOp X₀} (a : U ⟶ V) (b : Sec s₀ U.unop.1) :
    prSec w V.unop ((isAffine_aff V.unop).preimage pr) (mp (OAff s₀) a b) =
      Sec.res s₁ (pr.preimage_mono (leOfHom a.unop)) (prSec w U.unop ((isAffine_aff U.unop).preimage pr) b) :=
  (pairPull w).naturality (T := op ⟨(⟨pr ⁻¹ᵁ U.unop.1, (isAffine_aff U.unop).preimage pr⟩, U.unop), le_rfl⟩)
    (T' := op ⟨(⟨pr ⁻¹ᵁ V.unop.1, (isAffine_aff V.unop).preimage pr⟩, V.unop), le_rfl⟩)
    (homOfLE (show (⟨(⟨pr ⁻¹ᵁ V.unop.1, (isAffine_aff V.unop).preimage pr⟩, V.unop), le_rfl⟩ : Pair pr) ≤
      ⟨(⟨pr ⁻¹ᵁ U.unop.1, (isAffine_aff U.unop).preimage pr⟩, U.unop), le_rfl⟩ from
        ⟨pr.preimage_mono (leOfHom a.unop), leOfHom a.unop⟩)).op b

def tensCoef (w : pr ≫ s₀ = s₁ ≫ spMap (algebraMap R₀ R₁)) :
    CoefMap (RingHom.id R₁) (ext R₁ (OAff s₀)) (preAff pr ⋙ OAff s₁) :=
  natCoef (fun U ↦ (tensHom w U.unop ((isAffine_aff U.unop).preimage pr) : R₁ ⊗[R₀] Sec s₀ U.unop.1 →+* Sec s₁ (pr ⁻¹ᵁ U.unop.1)))
    (fun {U V} a b ↦ by
      change tensHom w V.unop _ (extHom R₁ (mp (OAff s₀) a) b) =
        Sec.res s₁ (pr.preimage_mono (leOfHom a.unop)) (tensHom w U.unop _ b)
      induction b using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul r x =>
        rw [Algebra.TensorProduct.map_tmul, tensHom_tmul, tensHom_tmul, map_mul, AlgHom.id_apply, prSec_res]
        congr 1
        exact ((Sec.res s₁ (pr.preimage_mono (leOfHom a.unop))).commutes r).symm
      | add x y hx hy => simp only [map_add, hx, hy])
    (fun U r b ↦ map_smul (tensHom w U.unop ((isAffine_aff U.unop).preimage pr)) r b)

variable {Y₀ Y₁ : Scheme.{0}} {pr' : Y₁ ⟶ Y₀} [IsAffineHom pr']

def pairBCObj (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (e : f₁ ≫ pr = pr' ≫ f₀) (p : Pair f₀) : Pair f₁ :=
  ⟨(⟨pr' ⁻¹ᵁ p.1.1.1, (isAffine_aff p.1.1).preimage pr'⟩,
    ⟨pr ⁻¹ᵁ p.1.2.1, (isAffine_aff p.1.2).preimage pr⟩), by
    change pr' ⁻¹ᵁ p.1.1.1 ≤ f₁ ⁻¹ᵁ pr ⁻¹ᵁ p.1.2.1
    rw [← Scheme.Hom.comp_preimage, e, Scheme.Hom.comp_preimage]
    exact pr'.preimage_mono p.2⟩

def pairBC (pr : X₁ ⟶ X₀) (pr' : Y₁ ⟶ Y₀) [IsAffineHom pr] [IsAffineHom pr'] {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (e : f₁ ≫ pr = pr' ≫ f₀) : (Pair f₀)ᵒᵖ ⥤ (Pair f₁)ᵒᵖ where
  obj p := op (pairBCObj pr pr' e p.unop)
  map {p q} a := (homOfLE (show pairBCObj pr pr' e q.unop ≤ pairBCObj pr pr' e p.unop from
    Subtype.coe_le_coe.1 (Prod.mk_le_mk.2 ⟨pr'.preimage_mono (Pair.le_fst (leOfHom a.unop)),
      pr.preimage_mono (Pair.le_snd (leOfHom a.unop))⟩))).op

variable {t₀ : Y₀ ⟶ Sp R₀} {t₁ : Y₁ ⟶ Sp R₁}

def tensPair (w' : pr' ≫ t₀ = t₁ ≫ spMap (algebraMap R₀ R₁)) {f₀ : Y₀ ⟶ X₀} {f₁ : Y₁ ⟶ X₁}
    (e : f₁ ≫ pr = pr' ≫ f₀) : CoefMap (RingHom.id R₁) (ext R₁ (OPair f₀ t₀)) (pairBC pr pr' e ⋙ OPair f₁ t₁) :=
  natCoef (fun p ↦ (tensCoef w').α ((pairFst f₀).obj p)) (fun a b ↦ (tensCoef w').naturality ((pairFst f₀).map a) b)
    (fun p r b ↦ (tensCoef w').smul ((pairFst f₀).obj p) r b)

end GlobalTheory.Obs.BC
