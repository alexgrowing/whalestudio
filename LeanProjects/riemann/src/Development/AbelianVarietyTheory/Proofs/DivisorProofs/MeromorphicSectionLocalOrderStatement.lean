import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeromorphicSectionLocalOrder
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meromorphic_section_local_order : ∀ (X : Type) [TopologicalSpace X] [T2Space X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas 1 X) (L : ReciprocityTheory.AnForm.M.LocPot X) (s : X → X → ℂ) (r : ℕ) (m : Fin r → ℕ) (P : Fin r → X), Function.Injective P → (∀ x : X, ∃ ψ : OpenPartialHomeomorph X (Fin 1 → ℂ), ReciprocityTheory.AnForm.M.IsCompatChart A ψ ∧ x ∈ ψ.source ∧ ∃ (n : ℕ) (u : (Fin 1 → ℂ) → ℂ), (∀ᶠ v in 𝓝 (ψ x), DifferentiableAt ℂ u v) ∧ u (ψ x) ≠ 0 ∧ (∀ᶠ v in 𝓝 (ψ x), s x (ψ.symm v) = u v * (v 0 - ψ x 0) ^ n) ∧ (∀ j, P j = x → n = m j) ∧ (x ∉ Set.range P → n = 0)) → ReciprocityTheory.AnForm.M.IsSNC A L s m (fun j => {P j}) := by
  first | exact @GlobalTheory.isSNC_of_local_power | exact GlobalTheory.isSNC_of_local_power | (intros; apply GlobalTheory.isSNC_of_local_power <;> assumption)
