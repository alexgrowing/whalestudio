import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicHolomorphicSectionsRegularAbelianVariety
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_holomorphic_sections_regular_abelianVariety : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ σ : M.ι → (Fin g → ℂ) → ℂ, (∀ i, DifferentiableOn ℂ (σ i) (pre u.ex (M.U i))) → (∀ i (l : u.Λ), ∀ z ∈ pre u.ex (M.U i), σ i (z + l) = σ i z) → (∀ i j, ∀ z ∈ pre u.ex (M.U i ⊓ M.U j), σ i z = val u.ex _ (M.g i j).val z * σ j z) → ∀ i, IsReg u.ex (M.U i) (σ i) := by
  first | exact @GlobalTheory.PeriodicSecAlg.main | exact GlobalTheory.PeriodicSecAlg.main | (intros; apply GlobalTheory.PeriodicSecAlg.main <;> assumption)
