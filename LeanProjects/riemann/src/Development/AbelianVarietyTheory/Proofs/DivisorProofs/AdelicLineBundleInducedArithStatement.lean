import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineBundleInducedArith
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open GlobalTheory GlobalTheory.ArInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_line_bundle_induced_arith : GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ {F : Type} [Field F] [NumberField F] {C : GlobalTheory.TrueGeo.CxSt F} (Y : GlobalTheory.ProjVar.Var F) {ι κ : Type} [Fintype ι] [Fintype κ] (e : κ ≃ ι) (A : ι → GlobalTheory.TrueGeo.Adl C Y), (∀ i, (A i).n = 1) → ∀ (M : GlobalTheory.TrueGeo.Model Y) (L : ι → GlobalTheory.HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), (∀ i, (A i).Induced M (L i) m 0) → (haveI := M.ar.isIntegral; IsArFun L Y.dim Ψ) → ∀ (V : GlobalTheory.Mean4O.Cover Y) (L' : κ → GlobalTheory.HermLB V.p) (Φ : MvPolynomial κ ℝ →ₗ[ℝ] ℝ), (∀ z, V.Induces (A (e z)) (L' z) 1) → IsArFun L' Y.dim Φ → ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ (Y.dim + 1)) / (((m : ℕ) : ℝ) ^ (Y.dim + 1) * (Module.finrank ℚ F : ℝ)) = Φ (lin (fun z => (n (e z) : ℝ)) ^ (Y.dim + 1)) / V.ν := by
  first | exact @GlobalTheory.CoverModelTop.top_eq | exact GlobalTheory.CoverModelTop.top_eq | (intros; apply GlobalTheory.CoverModelTop.top_eq <;> assumption)
