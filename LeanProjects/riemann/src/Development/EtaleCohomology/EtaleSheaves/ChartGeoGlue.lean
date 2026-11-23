import Development.EtaleCohomology.EtaleSheaves.LeafChartAffPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.ChartGeoPf

def ChartStdGeo : Prop := ∀ {X S : Scheme.{0}} (p : X ⟶ S) (n : ℕ) [SmoothOfRelativeDimension n p] (x : X)
  (W : X.Opens), x ∈ W → ∃ (U : S.Opens) (_ : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V)
    (hUV : V ≤ p ⁻¹ᵁ U), x ∈ V ∧ V ≤ W ∧ (p.appLE U V hUV).hom.IsStandardSmoothOfRelativeDimension n

def RangeKer : Prop := ∀ {X Z : Scheme.{0}} (ι : Z ⟶ X) [IsClosedImmersion ι] (V : X.Opens) (hV : IsAffineOpen V)
  (y : Spec Γ(X, V)), hV.fromSpec y ∈ Set.range ι ↔ RingHom.ker (ι.app V).hom ≤ (show PrimeSpectrum Γ(X, V) from y).asIdeal

def QuotLoc : Prop := ∀ (n : ℕ) (A B T : Type) [CommRing A] [CommRing B] [CommRing T] [Algebra A B] (π : B →+* T),
  Function.Surjective π → RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (π.comp (algebraMap A B)) →
  ∀ P : Ideal B, P.IsPrime → RingHom.ker π ≤ P → ∃ g ∉ P,
    Algebra.IsStandardSmoothOfRelativeDimension n A (Localization.Away g ⧸ (RingHom.ker π).map (algebraMap B (Localization.Away g)))

end LateralTheory.E.ChartGeoPf
