import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.MixedLower

def ChartMem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    {Xo : Moduli D l} {c : Coeff l}
    (Cn : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] (m : ℕ),
      (Fin m → LinearMap.BilinForm ℤ X) → Prop)
    (X : GMod Xo c) (J : X.X.IdealSheafData) (φ : InvFun (𝓞 E)) (N : ℕ) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X.X) (t : SAB H (Sp R)) (_ : SABMap t X.t ξ)
    (P : PELUnif (maximalIdeal R) t) (k : ℕ) (γ : Fin k → LinearMap.BilinForm ℤ P.D.toPre.X),
    IsCN R → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
    ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified → P.TorsionIso →
    Cn P.D.toPre.X k γ → InCone P.D.toPre γ →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ¬ (∀ p : ℕ, p.Prime → IsUnit (p : W)) →
      ∀ ϖ : W, Irreducible ϖ → ∀ f : R →+* W, IsLocalHom f → Set.range (jK W ≫ spMap f ≫ ξ) ⊆ Set.range X.j →
      ∀ be ∈ levelForms H 1 P.D.toPre.X, FormAt P.D.toPre f ϖ be →
      ∀ m : ℕ, (m : ℝ) = (comb 0 φ N φ).evalZ be → Ideal.span {ϖ ^ m} ≤ (idlAlong J ξ).map f

end GlobalTheory.MixedLower
