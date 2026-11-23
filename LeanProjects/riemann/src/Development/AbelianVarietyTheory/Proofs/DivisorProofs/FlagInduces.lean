import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB GlobalTheory.Mean4O GlobalTheory.TrueGeo GlobalTheory.ProjVar

namespace GlobalTheory.FlagInd

def FlagInduces {F : Type} [Field F] [NumberField F] {C : CxSt F} (Yv : Var F) {Bs : Scheme.{0}} (q : Bs ⟶ Sp (𝓞 F))
    {ι : Type} (E : ι → Bs.Modules) (n : ι → ℕ) (h : ∀ a, VMetric q (E a) (n a)) (H : ∀ a, (h a).IsCInf)
    (A : ∀ a, Fin (n a) → Adl C Yv) (Y : Scheme.{0}) [IsIntegral Y] (π : Y ⟶ Bs)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (arY : IsArithVar (π ≫ q) Yv.dim)
    (nY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y) : Prop :=
  ∃ (G : Scheme.{0}) (_ : IsIntegral G) (j : G ⟶ Y) (πG : G ⟶ Yv.X)
    (pb : IsPullback j (πG ≫ Yv.str) (π ≫ q) (spMap (algebraMap (𝓞 F) F)))
    (_ : IsFinite πG) (_ : Surjective πG) (φ : Yv.Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ Yv.X.fromSpecStalk (genericPoint Yv.X)),
    ∀ (a : ι) (i : Fin (n a)),
      (@Cover.mk _ _ Yv Y _ (π ≫ q) arY nY G _ j πG pb _ _ φ φs).Induces (A a i)
        (VMetric.grLB (fl a) i ((H a).pull π rfl)) 1

end GlobalTheory.FlagInd

end
