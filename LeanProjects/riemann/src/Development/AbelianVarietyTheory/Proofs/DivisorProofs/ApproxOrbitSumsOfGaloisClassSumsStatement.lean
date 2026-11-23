import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.approx_orbitSums_of_galois_classSums : ∀ (O : Type) [CommRing O] (bar : O → O) (q p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] (Φ : FPre bar q p A) (s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (N₁ N : ℕ) (y₀ : Φ.Y) (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin s → Φ.X y) → Q → PadicAlgCl p) (B : Type) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Finite (B ≃ₐ[A] B)], Function.Injective (algebraMap A B) → (∀ b : B, (∀ σ : B ≃ₐ[A] B, σ b = b) → b ∈ Set.range (algebraMap A B)) → ∀ 𝔷 : Ideal B, 𝔷.IsMaximal → 1 ≤ N → PosW W → (∀ y, IsUnimodMod O N (k y)) → Φ.ClassSums N₁ N y₀ k t B 𝔷 → Φ.OrbitSums W N₁ N y₀ k t := by
  first | exact @GlobalTheory.Poinc.OrbTrace.orbitSums_of_classSums | exact GlobalTheory.Poinc.OrbTrace.orbitSums_of_classSums | (intros; apply GlobalTheory.Poinc.OrbTrace.orbitSums_of_classSums <;> assumption)
