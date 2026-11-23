import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPartAttainsBoundUniqueShortestVector
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc.USum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightPart_attains_bound_unique_shortest_vector : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (m k : ℕ), S.N = m ^ 2 → 2 ≤ k → k ∣ m → ∀ ν : u.D.toPre.X, (∀ χ : u.D.toPre.X, m • χ ≠ 0 → l.q ν < l.q (ν + m • χ)) → ∃ h ∈ l.yy.ker, k • m • h = 0 ∧ ‖∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt (m • ν)) j ρ.i₀)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ = S.delta y₀ * Real.exp (-l.q ν) := by
  first | exact @GlobalTheory.UPoinc.ExactWeight.main | exact GlobalTheory.UPoinc.ExactWeight.main | (intros; apply GlobalTheory.UPoinc.ExactWeight.main <;> assumption)
