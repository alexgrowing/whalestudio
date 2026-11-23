import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreRationalFunctionRank
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieBaseIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_fibre_rational_function_rank : ∀ (D : D7) (O : Setup D) (B R : ℝ) (c : O.s.Comp) (G : Scheme.{0}) [IsIntegral G] (πG : G ⟶ (O.var c).X)
    (φ : (O.var c).Fn →+* G.functionField)
    (φs : G.fromSpecStalk (genericPoint G) ≫ πG = spMap φ ≫ (O.var c).X.fromSpecStalk (genericPoint (O.var c).X))
    (a : D.what₂.Tau × Bool) (i : Fin (rkB D.what₂.Tau O.N O.j a)) (hr : rkB D.what₂.Tau O.N O.j a = O.S.Dw.mult (embB D a))
    (x : G) (ρ : G.functionFieldˣ),
    (∀ t : (O.var c).Fnˣ, ((O.Φ.C c).gr (embB D a) (Fin.cast hr (cond a.2 i i.rev))).IsEqn (πG x) t →
      UnitAt x (φ (t : (O.var c).Fn) ^ (cond a.2 (-1 : ℤ) 1) * (ρ : G.functionField))) →
    UnitAt x (φ (genAt (adlOf (O.Φ.C c) (O.met.hm c) (rootSym O.S.Dw (ArIn.ind (setB O.Y B)) (some R) (DV.tauEmb D a.1)
      (cond a.2 0 O.j + i))).D (πG x)) ^ 1 * (ρ : G.functionField)) := by
  first | exact @GlobalTheory.RootEqn.unitAt_genAt_root | exact GlobalTheory.RootEqn.unitAt_genAt_root | (intros; apply GlobalTheory.RootEqn.unitAt_genAt_root <;> assumption)
