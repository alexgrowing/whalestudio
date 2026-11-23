import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalArithModelGenericPointMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_arith_model_generic_point_map : ∀ {F : Type} [Field F] [NumberField F] {C : TrueGeo.CxSt F} (Yv : ProjVar.Var F)
    (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (p : X ⟶ Sp (𝓞 F)) (p' : X' ⟶ Sp (𝓞 F))
    (ar : IsArithVar p Yv.dim) (nX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X)
    (ar' : IsArithVar p' Yv.dim) (nX' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X')
    (f : X' ⟶ X) (hf : f ≫ p = p') (G : Scheme.{0}) [IsIntegral G] (j : G ⟶ X) (j' : G ⟶ X'),
    j' ≫ f = j → ∀ (πG : G ⟶ Yv.X) [IsFinite πG] [Surjective πG]
    (pb : IsPullback j (πG ≫ Yv.str) p (spMap (algebraMap (𝓞 F) F)))
    (pb' : IsPullback j' (πG ≫ Yv.str) p' (spMap (algebraMap (𝓞 F) F)))
    (φ : Yv.Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ Yv.X.fromSpecStalk (genericPoint Yv.X))
    (A : TrueGeo.Adl C Yv) (L : HermLB p) (k : ℕ),
    (@Cover.mk _ _ Yv X _ p ar nX G _ j πG pb _ _ φ φs).Induces A L k →
      (@Cover.mk _ _ Yv X' _ p' ar' nX' G _ j' πG pb' _ _ φ φs).Induces A (L.pull f hf) k := by
  first | exact @GlobalTheory.Mean4O.Cover.induces_pull_of_comp | exact GlobalTheory.Mean4O.Cover.induces_pull_of_comp | (intros; apply GlobalTheory.Mean4O.Cover.induces_pull_of_comp <;> assumption)
