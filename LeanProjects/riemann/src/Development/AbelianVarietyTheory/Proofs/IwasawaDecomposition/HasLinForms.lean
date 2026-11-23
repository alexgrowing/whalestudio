import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef

section Vals

variable {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X]

theorem InvFun.evalZ_comb [Module.Finite O X] (a : ℕ) (ψ : InvFun O) (b : ℕ) (φ : InvFun O)
    (β : LinearMap.BilinForm ℤ X) : (comb a ψ b φ).evalZ β = a * ψ.evalZ β + b * φ.evalZ β := rfl

end Vals

theorem InvFun.eval_resInt {O : Type} [CommRing O] [Module.Finite ℤ O] (φ : InvFun ℤ) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] [Module.Finite ℤ X] (B : X → X → ℝ) : (resInt O φ).eval X B = φ.eval X B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [(resInt O φ).eval_eq hr]
  exact φ.eval_comp (r := r.restrictScalars ℤ) hr B

end GlobalTheory.TorRef

namespace GlobalTheory.TorRef

section Ord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def TraitOrd (φ : InvFun (𝓞 E)) (Z : Model Xo c β) (U : Z.X.Opens) (f : Γ(Z.X, U)) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ Z.X) (t : SAB H (Sp W)) (_ : SABMap t Z.t χ) (P : PELUnif (maximalIdeal W) t),
      Set.range (jK W ≫ χ) ⊆ Set.range Z.j → ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
      ∀ hU : χ (closedPoint W) ∈ U, ∃ n : ℕ, (n : ℝ) = φ.evalZ be ∧
        Associated ((Scheme.stalkClosedPointTo χ).hom ((Z.X.presheaf.germ U _ hU).hom f)) (ϖ ^ n)

end Ord

def HasLinForms {E : Type} [Field E] [NumberField E]
    (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop) (φ : InvFun (𝓞 E)) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
    Cn X m γ → ∃ ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, ∀ be : LinearMap.BilinForm ℤ X, (∀ y z, be y z = be z y) →
      ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal be = ∑ i, c i • toReal (γ i) → 0 ≤ ℓ be ∧ (ℓ be : ℝ) = φ.evalZ be

def ConeZr (E : Type) [Field E] [NumberField E] (g : ℕ) (φ : InvFun ℤ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  ConeZ E φ X m γ ∧ Module.Free ℤ X ∧ Module.finrank ℤ X ≤ g

end GlobalTheory.TorRef
