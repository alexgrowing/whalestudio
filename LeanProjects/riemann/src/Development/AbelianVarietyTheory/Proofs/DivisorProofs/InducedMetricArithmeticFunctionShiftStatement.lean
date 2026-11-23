import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedMetricArithmeticFunctionShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_metric_arithmetic_function_shift : Hypotheses2 → GlobalTheory.Published.RegularAlteration → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (ι : Type) [Fintype ι] (A : ι → Adl (cxSt F) Y) (L : ι → HermLB M.p) (m : ℕ+) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), (∀ i, (A i).Induced M (L i) m 0) → (haveI := M.ar.isIntegral; IsArFun L Y.dim Ψ) → ∀ (N : ℕ) (s s' : Fin N → ι), (∀ a, A (s' a) = { A (s a) with lg := (A (s' a)).lg }) → ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime ∧ ∃ n : ℕ, n ≠ 0 ∧ ∀ k : ℕ, RelFlag (fun a => A (s a)) (fun a => A (s' a)) p n k) → (∀ a v e y, resP v ∉ S → (A (s a)).lg v e y = (A (s' a)).lg v e y) → ∀ g : MvPolynomial ι ℝ, Ψ ((∑ a, X (s a) ^ 2 - ∑ a, X (s' a) ^ 2) * g) = 0 := by
  first | exact @GlobalTheory.LatChain.powerSum_two_eq | exact GlobalTheory.LatChain.powerSum_two_eq | (intros; apply GlobalTheory.LatChain.powerSum_two_eq <;> assumption)
