import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectoidLatticeSurjectiveProjection
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
open CategoryTheory WittVector GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published GlobalTheory.PerfdLat
open scoped ChangeOfRings Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perfectoid_lattice_surjective_projection : ∀ (p : ℕ) [Fact p.Prime] (D : PrismData p) (S : CycPerfd p) (G : PDivGroup p S.R) (c : ConstTate (eps S) G), Module.IsReflexive S.R G.dual.omega → ∃ pr : H D c 0 →ₗ[S.R] G.dual.omega, Function.Surjective pr ∧ (∀ x : H D c 0, (zeta S.ε 1 - 1) • pr x = c.al (x : Fin G.height → S.R)) ∧ ∀ x : H D c 0, pr x = 0 ↔ (x : Fin G.height → S.R) ∈ LinearMap.range c.alDual := by
  first | exact @GlobalTheory.PerfdLat.OmegaProj.exists_projection | exact GlobalTheory.PerfdLat.OmegaProj.exists_projection | (intros; apply GlobalTheory.PerfdLat.OmegaProj.exists_projection <;> assumption)
