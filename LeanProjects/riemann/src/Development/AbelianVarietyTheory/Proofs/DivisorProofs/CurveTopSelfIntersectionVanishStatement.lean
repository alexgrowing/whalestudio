import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveTopSelfIntersectionVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfCurveDegreesNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfSurjectivePullback
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.TrueGeo
open scoped ENNReal Classical
open Limits

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_top_self_intersection_vanish : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X X' : Scheme.{0}) (p : X ⟶ Sp k) (p' : X' ⟶ Sp k),
  IsProjOver p → IsProjOver p' → ∀ (ρ : X' ⟶ X), ρ ≫ p = p' → ∀ (r : ℕ) [Fact r.Prime]
  (Z : Scheme.{0}) (i : Z ⟶ X') [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod r) Γ(Z, ⊤)],
  topologicalKrullDim Z = 1 →
    (∀ L : LB X, L.IsLB → topSelfIntersection (ZMod r) ((L.pull ρ).pull i) 1 = 0) ∨
    ∃ (m : ℕ) (Z' : Scheme.{0}) (i' : Z' ⟶ X) (_ : IsClosedImmersion i') (_ : IsIntegral Z')
      (_ : Algebra (ZMod r) Γ(Z', ⊤)), topologicalKrullDim Z' = 1 ∧
      ∀ L : LB X, L.IsLB → topSelfIntersection (ZMod r) ((L.pull ρ).pull i) 1 = (m : ℤ) * topSelfIntersection (ZMod r) (L.pull i') 1 := by
  first | exact @GlobalTheory.CurveReduce.contracted_or_multiple | exact GlobalTheory.CurveReduce.contracted_or_multiple | (intros; apply GlobalTheory.CurveReduce.contracted_or_multiple <;> assumption)
