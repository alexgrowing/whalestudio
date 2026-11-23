import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureGenericFibreSpreadsFgSubalgebra
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelStructure_genericFibre_spreads_fg_subalgebra : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁) (P₁ : PolAV (Sp R₁)) {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [ArithBase o₂ Ω₂] [Algebra Ω₁ Ω₂] (κ : o₁ →+* o₂) (Q : PolAV (Sp Ω₂)) (φ : Q.A.left ⟶ P₁.A.left) (K : ℕ) (ze : o₂ˣ), R₁.FG → (∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) → FiniteDimensional Ω₁ Ω₂ → (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) → IsUnit (K : o₂) → Q.g = P₁.g → IsGrpPullback Q.A P₁.A (spMap ((algebraMap Ω₁ Ω₂).comp R₁.val.toRingHom)) φ → LBIso Q.L (P₁.L.pull φ) → Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze))) → ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R) (P : PolAV (Sp R)) (ψ : P.A.left ⟶ P₁.A.left), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a) ∧ P.g = P₁.g ∧ IsGrpPullback P.A P₁.A (spMap h) ψ ∧ LBIso P.L (P₁.L.pull ψ) ∧ Nonempty (Out.Level P K (unitOn ((Units.map (algebraMap o₂ R : o₂ →* R)) ze))) := by
  first | exact @GlobalTheory.LevelSpread.level_spreads | exact GlobalTheory.LevelSpread.level_spreads | (intros; apply GlobalTheory.LevelSpread.level_spreads <;> assumption)
