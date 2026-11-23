import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionCoordsThetaTimesRoots
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_sectionCoords_theta_times_roots : Out.Laws → Out.Laws2 → ∀ (g m N' : ℕ), Odd N' → m ^ 2 ∣ N' → ∃ (e : Ix g (N' ^ 2) → Ix g (N' ^ 2) → ℕ) (idx : Ix g (N' ^ 2) → Ix g (N' ^ 2) → Ix g (N' ^ 2)), ∀ (o : Type) [CommRing o] (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R) σ, x ≫ s = spMap β → t.HasTh x v → Ideal.span (Set.range v) = ⊤ → t.Emb m (Over.mk x) σ → ∀ h (y : Sp R ⟶ (Over.mk x ⊗ t.A).left), y = (lift (𝟙 (Over.mk x)) (((Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.lab h) ^ N')).left → ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧ p ∈ Set.range (spMap φ) ∧ SecCoord _ σ (spMap φ ≫ y) (fun a => φ (β (b.ζ ^ e a h : oˣ) * v (idx a h))) := by
  first | exact @GlobalTheory.torsion_secCoord | exact GlobalTheory.torsion_secCoord | (intros; apply GlobalTheory.torsion_secCoord <;> assumption)
