import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDualBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

namespace GlobalTheory.W1.Lef

def GermCompat {Z Y : Scheme.{0}} [IsIntegral Z] [IsIntegral Y] (c : Y ⟶ Z) (ψ : Z.functionField → Y.functionField) : Prop :=
  ∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)),
    ψ ((Z.presheaf.germ V (genericPoint Z) hV).hom g) = (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom (c.app V g)

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry KaehlerDifferential in

theorem _root_.GlobalTheory.W1.Lef.germCompat_id (Z : Scheme.{0}) [IsIntegral Z] :
    _root_.GlobalTheory.W1.Lef.GermCompat (𝟙 Z) (fun y => y) := by
  intro V hV hV' g
  rfl

abbrev omCx {K : Type} [Field K] [Algebra ℂ K] {ι : Type} [LinearOrder ι] (B : Finset ι → Subalgebra ℂ K) (a : ℕ) :
    Cx ℂ (Finset ι → DR ℂ K) := GlobalTheory.PD.cech fun I => omB ℂ K (B I) a

def mapL (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L] :
    DR ℂ K →ₗ[ℂ] DR ℂ L := (mapDR ℂ K L).toLinearMap.restrictScalars ℂ

theorem mapL_apply (K L : Type) [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    (ω : DR ℂ K) : mapL K L ω = mapDR ℂ K L ω := rfl

def mixMul {K L : Type} [Field K] [Field L] [Algebra ℂ K] [Algebra ℂ L] (φ₂ φ₁ : DR ℂ K →ₗ[ℂ] DR ℂ L) :
    DR ℂ K →ₗ[ℂ] DR ℂ K →ₗ[ℂ] DR ℂ L := (LinearMap.mul ℂ (DR ℂ L)).compl₁₂ φ₂ φ₁

def mixCover {Z Y : Scheme.{0}} {ι : Type} [LinearOrder ι] (c1 c2 : Y ⟶ Z) (U : ι → Z.Opens) : ι ×ₗ ι → Y.Opens :=
  fun S => c2 ⁻¹ᵁ U (fstL S) ⊓ c1 ⁻¹ᵁ U (sndL S)

abbrev CmpFam : Type 1 :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) [Smooth p] [Algebra ℂ X.functionField] (ι : Type) [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (B : Finset ι → Subalgebra ℂ X.functionField), IsAffCover p U B →
    ∀ a b : ℕ, hodgeH p a b ≃ₗ[ℂ] (omCx B a).H b

def NatPull (e : CmpFam) : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) [Smooth p] [Algebra ℂ X.functionField] (ι : Type) [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (B : Finset ι → Subalgebra ℂ X.functionField) (hU : IsAffCover p U B)
    (X' : Scheme.{0}) [IsIntegral X'] (p' : X' ⟶ Sp ℂ) [Smooth p'] [Algebra ℂ X'.functionField] (ι' : Type) [LinearOrder ι']
    [Fintype ι'] (U' : ι' → X'.Opens) (B' : Finset ι' → Subalgebra ℂ X'.functionField) (hU' : IsAffCover p' U' B')
    (f : X' ⟶ X) (hf : f ≫ p = p') (ψ : X.functionField →ₐ[ℂ] X'.functionField)
    (φ : DR ℂ X.functionField →ₗ[ℂ] DR ℂ X'.functionField) (τ : ι' → ι),
    IsDRMap ℂ ψ φ → GermCompat f ψ → (∀ i, U' i ≤ f ⁻¹ᵁ U (τ i)) →
    ∀ (a b : ℕ) (z : hodgeH p a b) (c : (omCx B a).Z b) (c' : (omCx B' a).Z b),
      e X p ι U B hU a b z = Submodule.Quotient.mk c →
      e X' p' ι' U' B' hU' a b (hodgePull hf a b z) = Submodule.Quotient.mk c' →
      c'.1 - pullC τ φ c.1 ∈ (omCx B' a).B b

def NatTrace (e : CmpFam) : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) [Smooth p] [Algebra ℂ X.functionField] (ι : Type) [LinearOrder ι] [Fintype ι]
    (U : ι → X.Opens) (B : Finset ι → Subalgebra ℂ X.functionField) (hU : IsAffCover p U B)
    (X' : Scheme.{0}) [IsIntegral X'] (p' : X' ⟶ Sp ℂ) [Smooth p'] [Algebra ℂ X'.functionField]
    (f : X' ⟶ X) [IsFinite f] [Etale f] (hf : f ≫ p = p') (B' : Finset ι → Subalgebra ℂ X'.functionField)
    (hU' : IsAffCover p' (fun i => f ⁻¹ᵁ U i) B')
    [Algebra X.functionField X'.functionField] [IsScalarTower ℂ X.functionField X'.functionField],
    GermCompat f (algebraMap X.functionField X'.functionField) →
    ∀ (a b : ℕ) (z : hodgeH p' a b) (c : (omCx B a).Z b) (c' : (omCx B' a).Z b),
      e X' p' ι (fun i => f ⁻¹ᵁ U i) B' hU' a b z = Submodule.Quotient.mk c' →
      e X p ι U B hU a b (hodgeTrace hf a b z) = Submodule.Quotient.mk c →
      c.1 - trC c'.1 ∈ (omCx B a).B b

def locTerm {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (a : ℕ) : ℂ :=
  (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C)).coeff a / (1 - A).det

example (A : Matrix (Fin 0) (Fin 0) ℂ) : locTerm A 0 = 1 := by simp [locTerm]

end GlobalTheory.W1.Lef
