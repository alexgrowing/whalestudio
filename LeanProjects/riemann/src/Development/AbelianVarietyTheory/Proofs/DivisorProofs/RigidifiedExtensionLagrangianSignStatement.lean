import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedExtensionLagrangianSign
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticesComplete
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.TwoSeq GlobalTheory.AbDatum GlobalTheory.DeRham GlobalTheory.AbDual GlobalTheory.ConjSeq GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.BadPt
open GlobalTheory.Cris (dp0)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidified_extension_lagrangian_sign : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K] (hR : (p : R) = 0) (hK : (p : K) = 0) (Γ' : PDivGroup p R) (𝒜 : PDivGroup p K) (κ : Γ'.baseChange K ⟶ 𝒜) (w : 𝒜 ⟶ 𝒜.dual) [Module R 𝒜.RigExt] [IsScalarTower R K 𝒜.RigExt] (B : LinearMap.BilinForm K 𝒜.RigExt) (ε : ℤˣ), Function.Bijective (omegaMap _ _ κ) → IsLagr B (LinearMap.range 𝒜.rigOfOmega) → (∀ (y : 𝒜.dual.RigExt) (b : CartierDual K (𝒜.A 1)), 𝒜.dual.IsConnecting (𝒜.dual.rigToExt y) b → ∀ (η' : 𝒜.omega) (a : 𝒜.A 1), dUnit K a = η'.1 1 → B (rigExtMap w y) (𝒜.rigOfOmega η') = ε • b a) → lattice κ w ⊔ (LinearMap.range 𝒜.rigOfOmega).restrictScalars R = B.dualSubmodule (latOmega κ) := by
  first | exact @GlobalTheory.BadPt.lattice_sup_range_eq_dualSubmodule | exact GlobalTheory.BadPt.lattice_sup_range_eq_dualSubmodule | (intros; apply GlobalTheory.BadPt.lattice_sup_range_eq_dualSubmodule <;> assumption)
