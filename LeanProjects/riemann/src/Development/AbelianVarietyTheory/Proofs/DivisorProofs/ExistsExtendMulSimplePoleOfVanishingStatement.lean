import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtendMulSimplePoleOfVanishing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplePoleAlong
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extend_mul_simplePole_of_vanishing : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} [IsReduced Y] {O : Y.Opens}, Dense (O : Set Y) → ∀ {P B N : LB Y} (C : ProdChart P B N) (ω : H0 p P O), GlobalTheory.LogCanonicalReflexive.SimplePoleAlong O C ω → ∀ g : H0 p B ⊤, (∀ y, y ∉ O → ∀ i hi, H0.germ i y (memTop y) hi g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) → ∃ G : H0 p N ⊤, H0.restr le_top G = C.mul ω (H0.restr le_top g) := by
  first | exact @GlobalTheory.LogCanonicalReflexive.exists_extend_mul_of_simplePole | exact GlobalTheory.LogCanonicalReflexive.exists_extend_mul_of_simplePole | (intros; apply GlobalTheory.LogCanonicalReflexive.exists_extend_mul_of_simplePole <;> assumption)
