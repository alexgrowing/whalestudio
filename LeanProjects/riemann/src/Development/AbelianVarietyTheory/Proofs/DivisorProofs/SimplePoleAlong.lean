import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogCanonicalReflexive

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k}

def SimplePoleAlong (O : Y.Opens) {P B N : LB Y} (C : ProdChart P B N) (ω : H0 p P O) : Prop :=
  ∀ y, y ∉ O → ∃ (V : Y.Opens) (_ : y ∈ V) (τ : C.τ) (ha : V ≤ P.U (C.a τ)) (_ : V ≤ B.U (C.b τ))
    (_ : V ≤ N.U (C.c τ)) (t u : Γ(Y, V)),
    (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ O) ∧ (∀ z (hz : z ∈ V), IsUnit (ger z hz u)) ∧
    (∀ (W : Y.Opens) (hW : W ≤ V) (f : Γ(Y, W)),
      (∀ z (hz : z ∈ W), z ∉ O → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) →
        ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) ∧
    ∀ z (hz : z ∈ V) (ho : z ∈ O), ger z hz t * H0.germ (C.a τ) z ho (ha hz) ω = ger z hz u

end GlobalTheory.LogCanonicalReflexive
