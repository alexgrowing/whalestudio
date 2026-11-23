import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramGradedSquareOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_graded_square_orthogonal : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {K : Type} [Field K] [NumberField K] {n : ℕ} (e : Fin n ≃ Letter Dw) (h : HermFam K (Fin n → K)) (σ : K →+* ℂ), (∀ z z' : Letter Dw, z.1 ≠ z'.1 → h.form σ (tauFr K e z.1 z.2) (tauFr K e z'.1 z'.2) = 0) → ∀ k : Fin (letters Dw).length, grSq (h.gram σ (allFr K e)) k = grSq (h.gram σ (tauFr K e ((letters Dw).get k).1)) ((letters Dw).get k).2 := by
  first | exact @GlobalTheory.LieSmooth.grSq_allFr_tauFr | exact GlobalTheory.LieSmooth.grSq_allFr_tauFr | (intros; apply GlobalTheory.LieSmooth.grSq_allFr_tauFr <;> assumption)
