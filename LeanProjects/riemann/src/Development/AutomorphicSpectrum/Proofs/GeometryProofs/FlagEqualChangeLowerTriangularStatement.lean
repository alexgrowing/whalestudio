import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagEqualChangeLowerTriangular
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_equal_change_lower_triangular : ∀ (Ω : Type) [Field Ω] (L : Type) [AddCommGroup L] [Module Ω L] (r : ℕ) (b b₀ : Fin r → L) (Tm : Matrix (Fin r) (Fin r) Ω), LinearIndependent Ω b → (∀ i : ℕ, flagStep Ω b i = flagStep Ω b₀ i) → (∀ i, b i = ∑ j, Tm i j • b₀ j) → LinearIndependent Ω b₀ ∧ ∀ i j, i < j → Tm i j = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri.independent_and_triangular | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri.independent_and_triangular | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.FlagTri.independent_and_triangular <;> assumption)
