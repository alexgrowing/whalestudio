import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoverInducedMetricsArith
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cover_induced_metrics_arith : GlobalTheory.Published.ArCalc → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (V : Cover Y) (ι : Type) [Fintype ι] (A : ι → Adl (cxSt F) Y) (L : ι → HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), (∀ i, (A i).Induced M (L i) m 0) → (haveI := M.ar.isIntegral; IsArFun L Y.dim Ψ) → ∃ (V' : Cover Y) (π : V'.X ⟶ V.X) (L' : ι → HermLB V'.p) (d : ℝ), π ≫ V.p = V'.p ∧ Lies V' V π ∧ d ≠ 0 ∧ (∀ i, Norms V' (L' i) (fun x => genAt (A i).D x ^ (m : ℕ)) (fun σ y => (m : ℕ) * lnAdl (A i) σ y) (fun v e y => (m : ℕ) * (A i).lg v e y)) ∧ IsArFun L' Y.dim (d • Ψ) := by
  first | exact @GlobalTheory.VertPass.pass | exact GlobalTheory.VertPass.pass | (intros; apply GlobalTheory.VertPass.pass <;> assumption)
