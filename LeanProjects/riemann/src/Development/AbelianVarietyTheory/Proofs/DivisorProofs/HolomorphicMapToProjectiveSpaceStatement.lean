import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMapToProjectiveSpace
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnimodularSolCoords
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_map_to_projective_space : ∀ (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ (N : ℕ) (φ : ℂ → (Sp ℂ ⟶ PSpace ℂ N)), (∀ z, φ z ≫ PSpace.str ℂ N = 𝟙 _) → (∀ z, ∀ l ∈ Λ.lattice, φ (z + l) = φ z) → (∀ (U : (PSpace ℂ N).Opens) (s : Γ(PSpace ℂ N, U)), IsOpen {z | ⊤ ≤ (φ z) ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun z => valAt' (φ z) U s) {z | ⊤ ≤ (φ z) ⁻¹ᵁ U}) → ∃ ψ : scheme (curve Λ Ω) ⟶ PSpace ℂ N, ψ ≫ PSpace.str ℂ N = toSpec (curve Λ Ω) ∧ ∀ z, pt Λ Ω z ≫ ψ = φ z := by
  first | exact @GlobalTheory.CMTorsion.exists_hom_of_periodic_holomorphic | exact GlobalTheory.CMTorsion.exists_hom_of_periodic_holomorphic | (intros; apply GlobalTheory.CMTorsion.exists_hom_of_periodic_holomorphic <;> assumption)
